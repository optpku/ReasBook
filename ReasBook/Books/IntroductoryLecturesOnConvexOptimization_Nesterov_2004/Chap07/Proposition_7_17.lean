/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Theorem_3_17
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Algorithm_7_6
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_26
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Definition_7_24
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Lemma_7_4
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Proposition_7_9
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap07.Theorem_7_6

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Asymptotics Filter
open scoped EllipsoidNotation PositiveDefMatrixNorm WeightedGramMatrix

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

/- Proposition 7.17 lies in Chapter 7's finite max-absolute-linear / ellipsoidal-rounding
complexity domain.

Sampled owner-style declarations:
- `CentralSymmetryRoundingAlgorithm` in `Algorithm_7_6`, the Chapter 7 source-facing owner of the
  finite-family iterative rounding run attached to `a₁, …, aₘ`;
- `CentralSymmetricRoundingMethod.stoppingIndex_isLeast` in `Algorithm_7_5`, the canonical
  first-hit stopping owner for the underlying centrally symmetric rounding method;
- mathlib `Asymptotics.IsBigO`, the canonical asymptotic owner behind `f =O[l] g`;
- `IsEllipsoidalRounding` in `Definition_7_29`, the chapter owner for centered
  `γ √n`-ellipsoidal roundings;
- `convexHull_range_union_neg_eq_absConvexHull_range` in `Proposition_7_12`, the bridge from the
  textbook symmetric hull `conv {± aᵢ}` to the canonical owner `absConvexHull ℝ (Set.range a)`.

Best owner abstraction:
- source-facing: a run of `CentralSymmetryRoundingAlgorithm` on the finite family
  `a₁, …, aₘ`;
- core/canonical: `IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ G` together with the
  first-hit stopping owner of the underlying Chapter 7 method;
- bridge/view: a first-hit witness, the stopping matrix, the explicit stopping-index bound, and
  the total arithmetic-work expression attached to the displayed explicit bound and its
  `O(n² (n + m) log m)` consequence.

Primitive data:
- the family `a : Fin m → E`;
- the admissibility data `1 ≤ n` and positive definiteness of the initial Gram matrix
  `centralSymmetryGramMatrix a`;
- a Chapter 7 run `algorithm : CentralSymmetryRoundingAlgorithm m n`;
- the identification of the run's internal stopping parameter with the textbook parameter `γ`;
- a canonical termination witness for the underlying centrally symmetric rounding method.

Derived API:
- the explicit stopping-index bound
  `maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ`;
- the explicit arithmetic-work bound
  `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ`;
- the canonical first-hit owner data
  `algorithm.toCentralSymmetricRoundingMethod.Terminates` and
  `algorithm.toCentralSymmetricRoundingMethod.stoppingIndex hTerminate`;
- the stopping matrix
  `algorithm.toCentralSymmetricRoundingMethod
    (algorithm.toCentralSymmetricRoundingMethod.stoppingIndex hTerminate)`;
- the canonical `=O` corollary for the explicit arithmetic-work bound on the admissible domain
  `m ≥ 2`.
- the existence theorem and the asymptotic corollary.

Source/core/bridge triage:
- source-facing: Proposition 7.17's existence claim for a terminating Algorithm 7.6 run on the
  given family `a₁, …, aₘ`;
- core/canonical: `CentralSymmetryRoundingAlgorithm`, `absConvexHull`, and
  `CentralSymmetricRoundingMethod.stoppingIndex_isLeast`, `IsEllipsoidalRounding`, and
  `Asymptotics.IsBigO`;
- bridge/view: the terminal matrix `method (method.stoppingIndex hTerminate)`, the explicit
  stopping-index bound, and the displayed work bound.
-/

/-- The explicit stopping-index upper bound
`(γ² / (γ - 1)²) log m` for the canonical first accepted iterate of the Chapter 7 centrally
symmetric rounding method attached to Proposition 7.17. -/
def maxAbsLinearSubdifferentialRoundingStoppingIndexBound
    (m : ℕ+) (γ : ℝ) : ℝ :=
  (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * Real.log (m : ℝ)

/-- Expanding `maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ` recovers the displayed
stopping-index expression `(γ² / (γ - 1)²) log m`. -/
theorem maxAbsLinearSubdifferentialRoundingStoppingIndexBound_eq
    (m : ℕ+) (γ : ℝ) :
    maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ =
      (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * Real.log (m : ℝ) :=
  rfl

/-- The displayed arithmetic-operation bound obtained by adding the preprocessing cost
`n² (n + 6m) / 6` and the rounding cost
`(γ² / (γ - 1)²) n² (2m + 3n) log m`. -/
def maxAbsLinearSubdifferentialRoundingArithmeticWorkBound
    (m : ℕ+) (n : ℕ) (γ : ℝ) : ℝ :=
  ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
    maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ * (n : ℝ) ^ (2 : ℕ) *
      (2 * (m : ℝ) + 3 * (n : ℝ))

-- Proof sketch: unfold
-- `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound`; the right-hand side is exactly the
-- displayed sum of the preprocessing and rounding contributions.
/-- Expanding `maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ` recovers the explicit
operation-count formula from Proposition 7.17. -/
theorem maxAbsLinearSubdifferentialRoundingArithmeticWorkBound_eq
    (m : ℕ+) (n : ℕ) (γ : ℝ) :
    maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ =
      ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
        (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * (n : ℝ) ^ (2 : ℕ) *
          (2 * (m : ℝ) + 3 * (n : ℝ)) * Real.log (m : ℝ) :=
  by
    simp [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound,
      maxAbsLinearSubdifferentialRoundingStoppingIndexBound, mul_assoc, mul_left_comm, mul_comm]

/-- Helper for Proposition 7.17: the initial Gram operator acts as the uniform average of the
rank-one maps `x ↦ ⟪aᵢ, x⟫ aᵢ`. -/
private lemma centralSymmetryGramMatrix_toEuclideanLin_eq_avg_smul
    {m : ℕ+} (a : Fin (m : ℕ) → E) (x : E) :
    (centralSymmetryGramMatrix a).toEuclideanLin x =
      ∑ i : Fin (m : ℕ), (((m : ℝ)⁻¹ * inner ℝ (a i) x)) • a i := by
  -- Expand the average Gram action into its rank-one summands.
  ext p
  simp [centralSymmetryGramMatrix, Matrix.toEuclideanLin_apply, Matrix.vecMulVec_mulVec, inner,
    dotProduct, mul_assoc]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hswap :
      ∑ x_1, (a i).ofLp x_1 * x.ofLp x_1 =
        ∑ x_1, x.ofLp x_1 * (a i).ofLp x_1 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hswap]
  ring

/-- Helper for Proposition 7.17: the initial Gram quadratic form is the uniform average of the
squared pairings `|⟪aᵢ, x⟫|^2`. -/
private lemma centralSymmetryGramMatrix_quadratic_eq_avg_sq_inner
    {m : ℕ+} (a : Fin (m : ℕ) → E) (x : E) :
    inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x =
      (m : ℝ)⁻¹ * ∑ i : Fin (m : ℕ), (inner ℝ (a i) x) ^ (2 : ℕ) := by
  -- Rewrite the operator action by the explicit average rank-one formula.
  rw [centralSymmetryGramMatrix_toEuclideanLin_eq_avg_smul]
  -- Then distribute the inner product over the finite sum and identify each square.
  rw [sum_inner]
  calc
    ∑ i : Fin (m : ℕ), inner ℝ ((((m : ℝ)⁻¹ * inner ℝ (a i) x)) • a i) x
        = ∑ i : Fin (m : ℕ), (m : ℝ)⁻¹ * (inner ℝ (a i) x) ^ (2 : ℕ) := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [real_inner_smul_left]
            ring
    _ = (m : ℝ)⁻¹ * ∑ i : Fin (m : ℕ), (inner ℝ (a i) x) ^ (2 : ℕ) := by
          rw [Finset.mul_sum]

/-- Helper for Proposition 7.17: the support function of the canonical body dominates the initial
Gram norm. -/
private lemma initialGramNorm_le_maxTypeObjective_absInner
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hGram : (centralSymmetryGramMatrix a).PosDef) (x : E) :
    ‖x‖[⟨centralSymmetryGramMatrix a, hGram⟩] ≤
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.2
  have hmax_le :
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤ M := by
    simpa [M]
  rw [maxTypeObjective_le_iff] at hmax_le
  have hM_nonneg : 0 ≤ M := by
    let i0 : Fin (m : ℕ) := ⟨0, m.2⟩
    exact le_trans (abs_nonneg _) (hmax_le i0)
  have hquad_nonneg :
      0 ≤ inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x := by
    -- Positive definiteness of the Gram matrix makes its quadratic form nonnegative.
    have hPosLin : (centralSymmetryGramMatrix a).toEuclideanLin.IsPositive := by
      exact (Matrix.isPositive_toEuclideanLin_iff).2 hGram.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  have hterm_le : ∀ i : Fin (m : ℕ), (inner ℝ (a i) x) ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
    intro i
    have hle : |inner ℝ (a i) x| ≤ M := hmax_le i
    calc
      (inner ℝ (a i) x) ^ (2 : ℕ) = |inner ℝ (a i) x| ^ (2 : ℕ) := by rw [sq_abs]
      _ ≤ M ^ (2 : ℕ) := by
            have hsq : |inner ℝ (a i) x| ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
              exact sq_le_sq.mpr <| by simpa [abs_of_nonneg hM_nonneg] using hle
            simpa using hsq
  have hsum_le :
      ∑ i : Fin (m : ℕ), (inner ℝ (a i) x) ^ (2 : ℕ) ≤
        ∑ i : Fin (m : ℕ), M ^ (2 : ℕ) := by
    -- Replace each squared pairing by the common extremal square `M^2`.
    exact Finset.sum_le_sum fun i _ ↦ hterm_le i
  have hquad_le :
      inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x ≤ M ^ (2 : ℕ) := by
    calc
      inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x
          = (m : ℝ)⁻¹ * ∑ i : Fin (m : ℕ), (inner ℝ (a i) x) ^ (2 : ℕ) := by
              rw [centralSymmetryGramMatrix_quadratic_eq_avg_sq_inner]
      _ ≤ (m : ℝ)⁻¹ * ∑ i : Fin (m : ℕ), M ^ (2 : ℕ) := by
            exact mul_le_mul_of_nonneg_left hsum_le (inv_nonneg.mpr hm_pos.le)
      _ = M ^ (2 : ℕ) := by
            simp [hm_pos.ne', mul_assoc, mul_left_comm, mul_comm]
  -- Finish by taking square roots on both sides of the quadratic estimate.
  rw [positiveDefMatrixNorm_def ⟨centralSymmetryGramMatrix a, hGram⟩]
  have hsqrt_le := Real.sqrt_le_sqrt hquad_le
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hM_nonneg] at hsqrt_le
  exact hsqrt_le

/-- Helper for Proposition 7.17: the initial support-function objective is controlled by
`sqrt m` times the norm induced by the initial Gram matrix. -/
private lemma maxTypeObjective_absInner_le_sqrt_card_mul_initialGramNorm
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hGram : (centralSymmetryGramMatrix a).PosDef) (x : E) :
    maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤
      Real.sqrt (m : ℝ) * ‖x‖[⟨centralSymmetryGramMatrix a, hGram⟩] := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.2
  have hquad_nonneg :
      0 ≤ inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x := by
    -- Positive definiteness of the initial Gram matrix makes its quadratic form nonnegative.
    have hPosLin : (centralSymmetryGramMatrix a).toEuclideanLin.IsPositive := by
      exact (Matrix.isPositive_toEuclideanLin_iff).2 hGram.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  rw [maxTypeObjective_le_iff]
  intro i
  have hsingle_le :
      (inner ℝ (a i) x) ^ (2 : ℕ) ≤
        ∑ j : Fin (m : ℕ), (inner ℝ (a j) x) ^ (2 : ℕ) := by
    -- One nonnegative summand is bounded by the full sum of squares.
    simpa using
      (Finset.single_le_sum
        (fun j _ ↦ sq_nonneg (inner ℝ (a j) x))
        (by simp : i ∈ (Finset.univ : Finset (Fin (m : ℕ)))))
  have hquad_eq :
      ∑ j : Fin (m : ℕ), (inner ℝ (a j) x) ^ (2 : ℕ) =
        (m : ℝ) * inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x := by
    -- Clear the averaging factor in the Gram quadratic-form identity.
    calc
      ∑ j : Fin (m : ℕ), (inner ℝ (a j) x) ^ (2 : ℕ) =
          (m : ℝ) * ((m : ℝ)⁻¹ *
            ∑ j : Fin (m : ℕ), (inner ℝ (a j) x) ^ (2 : ℕ)) := by
              field_simp [hm_pos.ne']
      _ = (m : ℝ) * inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x := by
            rw [centralSymmetryGramMatrix_quadratic_eq_avg_sq_inner]
  have hsq_le :
      (inner ℝ (a i) x) ^ (2 : ℕ) ≤
        (Real.sqrt (m : ℝ) * ‖x‖[⟨centralSymmetryGramMatrix a, hGram⟩]) ^ (2 : ℕ) := by
    -- Rewrite both sides in the same quadratic scale and compare the squares directly.
    rw [positiveDefMatrixNorm_def ⟨centralSymmetryGramMatrix a, hGram⟩]
    calc
      (inner ℝ (a i) x) ^ (2 : ℕ) ≤
          ∑ j : Fin (m : ℕ), (inner ℝ (a j) x) ^ (2 : ℕ) := hsingle_le
      _ = (m : ℝ) * inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x := hquad_eq
      _ = (Real.sqrt (m : ℝ) *
            Real.sqrt (inner ℝ ((centralSymmetryGramMatrix a).toEuclideanLin x) x)) ^ (2 : ℕ) := by
            nlinarith [Real.sq_sqrt hm_pos.le, Real.sq_sqrt hquad_nonneg]
  have hbound_nonneg :
      0 ≤ Real.sqrt (m : ℝ) * ‖x‖[⟨centralSymmetryGramMatrix a, hGram⟩] := by
    positivity
  -- Take square roots through the nonnegative right-hand side to recover the absolute-value bound.
  have habs_le :=
    (sq_le_sq.mp <| by
      simpa [sq_abs] using hsq_le)
  simpa [abs_of_nonneg hbound_nonneg] using habs_le

/-- Helper for Proposition 7.17: a weighted Gram matrix acts as the weighted sum of the rank-one
operators `x ↦ ⟪aᵢ, x⟫ aᵢ`. -/
private lemma weightedGramMatrix_toEuclideanLin_eq_sum_weights_smul
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ))) (x : E) :
    (B[a](weights.weights)).toEuclideanLin x =
      ∑ i : Fin (m : ℕ), (weights.weights i * inner ℝ (a i) x) • a i := by
  -- Expand the weighted Gram action entrywise and isolate each rank-one contribution.
  ext p
  simp [weightedGramMatrix, Matrix.toEuclideanLin_apply, Matrix.vecMulVec_mulVec, inner,
    dotProduct, mul_assoc]
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hswap :
      ∑ x_1, (a i).ofLp x_1 * x.ofLp x_1 =
        ∑ x_1, x.ofLp x_1 * (a i).ofLp x_1 := by
    refine Finset.sum_congr rfl ?_
    intro j hj
    ring
  rw [hswap]
  ring

/-- Helper for Proposition 7.17: the quadratic form of a weighted Gram matrix is the weighted sum
of the squared pairings `|⟪aᵢ, x⟫|^2`. -/
private lemma weightedGramMatrix_quadratic_eq_sum_weights_mul_sq_inner
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ))) (x : E) :
    inner ℝ ((B[a](weights.weights)).toEuclideanLin x) x =
      ∑ i : Fin (m : ℕ), weights.weights i * (inner ℝ (a i) x) ^ (2 : ℕ) := by
  -- Rewrite the operator through the weighted rank-one expansion.
  rw [weightedGramMatrix_toEuclideanLin_eq_sum_weights_smul]
  -- Then evaluate the inner product termwise and identify each square.
  rw [sum_inner]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [real_inner_smul_left]
  ring

/-- Helper for Proposition 7.17: whenever `G = B[a](weights.weights)` is a simplex-weighted Gram
matrix, its primal norm is controlled by the support function of `absConvexHull ℝ (Set.range a)`.
-/
private lemma weightedGramNorm_le_maxTypeObjective_absInner
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ)))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (hrep : G = B[a](weights.weights)) (x : E) :
    ‖x‖[⟨G, hG⟩] ≤
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x := by
  let M : ℝ := maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x
  have hmax_le :
      maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x ≤ M := by
    simpa [M]
  rw [maxTypeObjective_le_iff] at hmax_le
  have hweights_total : ∑ i : Fin (m : ℕ), weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have hM_nonneg : 0 ≤ M := by
    let i0 : Fin (m : ℕ) := ⟨0, m.2⟩
    exact le_trans (abs_nonneg _) (hmax_le i0)
  have hterm_le :
      ∀ i : Fin (m : ℕ),
        weights.weights i * (inner ℝ (a i) x) ^ (2 : ℕ) ≤
          weights.weights i * M ^ (2 : ℕ) := by
    intro i
    have hle : |inner ℝ (a i) x| ≤ M := hmax_le i
    have hsq :
        (inner ℝ (a i) x) ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by
      calc
        (inner ℝ (a i) x) ^ (2 : ℕ) = |inner ℝ (a i) x| ^ (2 : ℕ) := by rw [sq_abs]
        _ ≤ M ^ (2 : ℕ) := by
              exact sq_le_sq.mpr <| by simpa [abs_of_nonneg hM_nonneg] using hle
    exact mul_le_mul_of_nonneg_left hsq (weights.nonneg i)
  have hsum_le :
      ∑ i : Fin (m : ℕ), weights.weights i * (inner ℝ (a i) x) ^ (2 : ℕ) ≤
        ∑ i : Fin (m : ℕ), weights.weights i * M ^ (2 : ℕ) := by
    -- Replace each squared pairing by the common extremal square `M^2`.
    exact Finset.sum_le_sum fun i _ ↦ hterm_le i
  have hquad_le : inner ℝ (G.toEuclideanLin x) x ≤ M ^ (2 : ℕ) := by
    calc
      inner ℝ (G.toEuclideanLin x) x
          = ∑ i : Fin (m : ℕ), weights.weights i * (inner ℝ (a i) x) ^ (2 : ℕ) := by
              rw [hrep, weightedGramMatrix_quadratic_eq_sum_weights_mul_sq_inner]
      _ ≤ ∑ i : Fin (m : ℕ), weights.weights i * M ^ (2 : ℕ) := hsum_le
      _ = M ^ (2 : ℕ) := by
            rw [← Finset.sum_mul, hweights_total, one_mul]
  -- Finish by taking square roots on both sides of the quadratic estimate.
  rw [positiveDefMatrixNorm_def ⟨G, hG⟩]
  have hsqrt_le := Real.sqrt_le_sqrt hquad_le
  rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hM_nonneg] at hsqrt_le
  exact hsqrt_le

/-- Helper for Proposition 7.17: the canonical absolutely convex hull of the generators is
compact because it is the convex hull of the finite symmetric set `{± aᵢ}`. -/
lemma absConvexHull_range_isCompact
    {m : ℕ+} (a : Fin (m : ℕ) → E) :
    IsCompact (absConvexHull ℝ (Set.range a)) := by
  -- Rewrite the body as a convex hull of a finite generating set and use compactness of finite
  -- convex hulls.
  have hfinite :
      (Set.range a ∪ Set.range (fun i : Fin (m : ℕ) ↦ -a i)).Finite := by
    exact (Set.finite_range a).union (Set.finite_range fun i : Fin (m : ℕ) ↦ -a i)
  have hcompact :
      IsCompact (convexHull ℝ (Set.range a ∪ Set.range fun i : Fin (m : ℕ) ↦ -a i)) :=
    by
      simpa using hfinite.isCompact_convexHull ℝ
  simpa [convexHull_range_union_neg_eq_absConvexHull_range] using hcompact

/-- Helper for Proposition 7.17: the canonical absolutely convex hull is nonempty because it
contains the generating family. -/
lemma absConvexHull_range_nonempty
    {m : ℕ+} (a : Fin (m : ℕ) → E) :
    (absConvexHull ℝ (Set.range a)).Nonempty := by
  -- Use the first generator to witness nonemptiness of the range and then pass to the
  -- absolutely convex hull.
  have hrange_nonempty : (Set.range a).Nonempty := by
    refine ⟨a ⟨0, m.2⟩, ?_⟩
    exact ⟨⟨0, m.2⟩, rfl⟩
  exact hrange_nonempty.absConvexHull

/-- Helper for Proposition 7.17: `absConvexHull ℝ (Set.range a)` is the canonical convex body on
which Algorithm 7.6 runs. -/
def absConvexHull_range_body
    {m : ℕ+} (a : Fin (m : ℕ) → E) : ConvexBody E :=
  { carrier := absConvexHull ℝ (Set.range a)
    convex' := convex_absConvexHull
    isCompact' := absConvexHull_range_isCompact a
    nonempty' := absConvexHull_range_nonempty a }

/-- Helper for Proposition 7.17: the canonical absolutely convex hull is balanced, matching the
owner-side symmetry requirement of `CentralSymmetricRoundingMethod`. -/
lemma absConvexHull_range_body_balanced
    {m : ℕ+} (a : Fin (m : ℕ) → E) :
    Balanced ℝ ((absConvexHull_range_body a : ConvexBody E) : Set E) := by
  -- The absolutely convex hull is balanced by the canonical mathlib owner theorem.
  simpa [absConvexHull_range_body] using
    (balanced_absConvexHull : Balanced ℝ (absConvexHull ℝ (Set.range a)))

/-- Helper for Proposition 7.17: for every inverse matrix candidate `H`, one generator attains
the maximum score `i ↦ ⟪aᵢ, H aᵢ⟫` on the finite index set. -/
lemma exists_score_maximizer
    {m : ℕ+} (a : Fin (m : ℕ) → E) (H : Matrix (Fin n) (Fin n) ℝ) :
    ∃ i : Fin (m : ℕ), IsMaxOn (fun j ↦ centralSymmetryScore a H j) Set.univ i := by
  -- Choose a maximizing index on the finite domain `Fin m` and rewrite the result on `Set.univ`.
  obtain ⟨i, -, hi⟩ :=
    Finset.univ.exists_max_image
      (fun j : Fin (m : ℕ) ↦ centralSymmetryScore a H j)
      ⟨⟨0, m.2⟩, by simp⟩
  refine ⟨i, ?_⟩
  rw [isMaxOn_univ_iff]
  intro j
  exact hi j (by simp)

/-- Helper for Proposition 7.17: choose a canonical maximizing generator index for the current
score matrix. -/
noncomputable def scoreMaximizingIndex
    {m : ℕ+} (a : Fin (m : ℕ) → E) (H : Matrix (Fin n) (Fin n) ℝ) :
    Fin (m : ℕ) :=
  Classical.choose (exists_score_maximizer a H)

/-- Helper for Proposition 7.17: the chosen index `scoreMaximizingIndex a H` realizes the maximum
of the current score function on `Fin m`. -/
lemma scoreMaximizingIndex_isMaxOn
    {m : ℕ+} (a : Fin (m : ℕ) → E) (H : Matrix (Fin n) (Fin n) ℝ) :
    IsMaxOn (fun j ↦ centralSymmetryScore a H j) Set.univ (scoreMaximizingIndex a H) := by
  -- Unfold the choice and use the specification of `Classical.choose`.
  exact Classical.choose_spec (exists_score_maximizer a H)

/-- Helper for Proposition 7.17: for a positive-definite matrix `G`, the quadratic score
`⟪aᵢ, G⁻¹ aᵢ⟫` is exactly the square of the `G`-dual norm of the generator `aᵢ`. -/
lemma centralSymmetryScore_inv_eq_dualNorm_sq
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (i : Fin (m : ℕ)) :
    centralSymmetryScore a G⁻¹ i = ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
  have hinner_nonneg :
      0 ≤ inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)) := by
    -- Positive definiteness of `G⁻¹` makes the quadratic score nonnegative.
    have hPosLin : (Matrix.toEuclideanLin G⁻¹).IsPositive := by
      exact (Matrix.isPositive_toEuclideanLin_iff).2 hG.inv.posSemidef
    exact hPosLin.inner_nonneg_right (a i)
  -- Rewrite the score through the dual norm and square the explicit square-root formula.
  calc
    centralSymmetryScore a G⁻¹ i
        = inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)) := by
            rfl
    _ = (Real.sqrt (inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)))) ^ (2 : ℕ) := by
          symm
          exact Real.sq_sqrt hinner_nonneg
    _ = ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
          rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a i)]

/-- Helper for Proposition 7.17: if a generator maximizes the score
`j ↦ ⟪aⱼ, G⁻¹ aⱼ⟫`, then it also maximizes the `G`-dual norm among the generators. -/
lemma dualNorm_le_of_score_isMaxOn
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) {i : Fin (m : ℕ)}
    (hi : IsMaxOn (fun j ↦ centralSymmetryScore a G⁻¹ j) Set.univ i) :
    ∀ j : Fin (m : ℕ), ‖a j‖[⟨G, hG⟩,*] ≤ ‖a i‖[⟨G, hG⟩,*] := by
  rw [isMaxOn_univ_iff] at hi
  intro j
  have hscore :=
    hi j
  rw [centralSymmetryScore_inv_eq_dualNorm_sq a hG j,
    centralSymmetryScore_inv_eq_dualNorm_sq a hG i] at hscore
  have hj_nonneg : 0 ≤ ‖a j‖[⟨G, hG⟩,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a j)]
    exact Real.sqrt_nonneg _
  have hi_nonneg : 0 ≤ ‖a i‖[⟨G, hG⟩,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a i)]
    exact Real.sqrt_nonneg _
  nlinarith

/-- Helper for Proposition 7.17: the canonical chosen score maximizer dominates every generator in
`G`-dual norm. -/
lemma dualNorm_le_scoreMaximizingIndex
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (j : Fin (m : ℕ)) :
    ‖a j‖[⟨G, hG⟩,*] ≤ ‖a (scoreMaximizingIndex a G⁻¹)‖[⟨G, hG⟩,*] := by
  -- Specialize the previous generator-maximization lemma to the canonical chosen index.
  exact dualNorm_le_of_score_isMaxOn a hG
    (scoreMaximizingIndex_isMaxOn a G⁻¹) j

/-- Helper for Proposition 7.17: the generator maximizing
`j ↦ ⟪aⱼ, G⁻¹ aⱼ⟫` also maximizes the `G`-dual norm on the whole body
`absConvexHull ℝ (Set.range a)`. -/
lemma scoreMaximizingIndex_isMaxOn_absConvexHull_dualNorm
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) :
    let i := scoreMaximizingIndex a G⁻¹
    a i ∈ absConvexHull ℝ (Set.range a) ∧
      IsMaxOn (fun g : E ↦ ‖g‖[⟨G, hG⟩,*])
        (absConvexHull ℝ (Set.range a)) (a i) := by
  classical
  let i := scoreMaximizingIndex a G⁻¹
  refine ⟨subset_absConvexHull (Set.mem_range_self i), ?_⟩
  rw [isMaxOn_iff]
  intro g hg
  -- Rewrite the dual norm as a support-function supremum over the primal unit ball.
  rw [positiveDefMatrixNorm_dualNorm_apply]
  refine csSup_le ?_ ?_
  · refine ⟨(0 : ℝ), (0 : E), ?_⟩
    constructor
    · change (positiveDefMatrixNorm G hG) 0 ≤ 1
      simp
    · simp
  · rintro y ⟨x, hx, rfl⟩
    have hx_nonneg : 0 ≤ ‖x‖[⟨G, hG⟩] := by
      rw [positiveDefMatrixNorm_def ⟨G, hG⟩]
      exact Real.sqrt_nonneg _
    obtain ⟨s, hs_mem, hs_max⟩ := (absConvexHull_range_body a).exists_isMaxOn_inner x
    have hs_sup :
        sSup ((fun t : E ↦ inner ℝ t x) '' ((absConvexHull_range_body a : ConvexBody E) : Set E)) =
          inner ℝ s x := by
      have hs_lub :
          IsLUB
            ((fun t : E ↦ inner ℝ t x) '' ((absConvexHull_range_body a : ConvexBody E) : Set E))
            (inner ℝ s x) := by
        simpa [isMaxOn_iff] using hs_max.isLUB hs_mem
      exact hs_lub.csSup_eq ⟨inner ℝ s x, ⟨s, hs_mem, rfl⟩⟩
    have hinner_le_body :
        inner ℝ g x ≤ (absConvexHull_range_body a).supportFunctionReal x := by
      calc
        inner ℝ g x ≤ inner ℝ s x := hs_max hg
        _ = sSup ((fun t : E ↦ inner ℝ t x) '' ((absConvexHull_range_body a : ConvexBody E) : Set E)) := by
              symm
              exact hs_sup
        _ = (absConvexHull_range_body a).supportFunctionReal x := by
              symm
              exact ConvexBody.supportFunctionReal_eq_sSup_inner (absConvexHull_range_body a) x
    have hsupport_eq :
        (absConvexHull_range_body a).supportFunctionReal x =
          maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x := by
      simpa [absConvexHull_range_body] using
        (supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a x)
    have hmax_le :
        maxTypeObjective (fun j y ↦ |inner ℝ (a j) y|) x ≤
          ‖a i‖[⟨G, hG⟩,*] := by
      rw [maxTypeObjective_le_iff]
      intro j
      have hj_nonneg : 0 ≤ ‖a j‖[⟨G, hG⟩,*] := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a j)]
        exact Real.sqrt_nonneg _
      have habs_inner_le :
          |inner ℝ (a j) x| ≤ ‖a j‖[⟨G, hG⟩,*] * ‖x‖[⟨G, hG⟩] := by
        by_cases h_nonneg : 0 ≤ inner ℝ (a j) x
        · have hinner :=
            Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G hG) x (a j)
          simpa [abs_of_nonneg h_nonneg, mul_comm] using hinner
        · have hinner :=
            Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm G hG) (-x) (a j)
          have habs_eq : |inner ℝ (a j) x| = inner ℝ (a j) (-x) := by
            calc
              |inner ℝ (a j) x| = -inner ℝ (a j) x := by
                exact abs_of_nonpos (le_of_not_ge h_nonneg)
              _ = inner ℝ (a j) (-x) := by simp
          calc
            |inner ℝ (a j) x| = inner ℝ (a j) (-x) := habs_eq
            _ ≤ ‖a j‖[⟨G, hG⟩,*] * ‖-x‖[⟨G, hG⟩] := by
                  simpa [mul_comm] using hinner
            _ = ‖a j‖[⟨G, hG⟩,*] * ‖x‖[⟨G, hG⟩] := by
                  simp
      calc
        |inner ℝ (a j) x| ≤ ‖a j‖[⟨G, hG⟩,*] * ‖x‖[⟨G, hG⟩] := habs_inner_le
        _ ≤ ‖a j‖[⟨G, hG⟩,*] * 1 := by
              exact mul_le_mul_of_nonneg_left hx hj_nonneg
        _ = ‖a j‖[⟨G, hG⟩,*] := by ring
        _ ≤ ‖a i‖[⟨G, hG⟩,*] := by
              simpa [i] using dualNorm_le_scoreMaximizingIndex a hG j
    exact le_trans (by rwa [hsupport_eq] at hinner_le_body) hmax_le

/-- Helper for Proposition 7.17: the owner-side radius of the body
`absConvexHull ℝ (Set.range a)` is realized by the canonical score-maximizing generator. -/
lemma centralSymmetricRoundingRadius_eq_scoreMaximizingIndex_selectedRadius
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) :
    centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩ =
      centralSymmetrySelectedRadius a G⁻¹ (scoreMaximizingIndex a G⁻¹) := by
  let i := scoreMaximizingIndex a G⁻¹
  rcases scoreMaximizingIndex_isMaxOn_absConvexHull_dualNorm a hG with ⟨hi_mem, hi_max⟩
  have hi_lub :
      IsLUB
        ((fun g : E ↦ ‖g‖[⟨G, hG⟩,*]) '' ((absConvexHull_range_body a : ConvexBody E) : Set E))
        ‖a i‖[⟨G, hG⟩,*] := by
    simpa [i, isMaxOn_iff] using hi_max.isLUB hi_mem
  have hsSup_eq :
      sSup ((fun g : E ↦ ‖g‖[⟨G, hG⟩,*]) '' ((absConvexHull_range_body a : ConvexBody E) : Set E)) =
        ‖a i‖[⟨G, hG⟩,*] :=
    hi_lub.csSup_eq ⟨‖a i‖[⟨G, hG⟩,*], ⟨a i, hi_mem, rfl⟩⟩
  have hi_nonneg : 0 ≤ ‖a i‖[⟨G, hG⟩,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a i)]
    exact Real.sqrt_nonneg _
  have hsqrt_eq :
      Real.sqrt (‖a i‖[⟨G, hG⟩,*] * ‖a i‖[⟨G, hG⟩,*]) =
        ‖a i‖[⟨G, hG⟩,*] := by
    rw [← pow_two, Real.sqrt_sq_eq_abs, abs_of_nonneg hi_nonneg]
  -- Identify the owner-side radius with the chosen generator norm, then rewrite that norm as the
  -- selected radius.
  rw [centralSymmetricRoundingRadius_eq_sSup, hsSup_eq, centralSymmetrySelectedRadius,
    centralSymmetryScore_inv_eq_dualNorm_sq a hG i, pow_two]
  exact hsqrt_eq.symm

/-- Helper for Proposition 7.17: any positive-definite matrix whose primal norm is dominated by
the support function of `absConvexHull ℝ (Set.range a)` has its unit ellipsoid inside that body.
-/
private lemma unitEllipsoid_subset_absConvexHull_of_norm_bound
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef)
    (hnorm_le :
      ∀ x : E,
        ‖x‖[⟨G, hG⟩] ≤
          maxTypeObjective (fun i y ↦ |inner ℝ (a i) y|) x) :
    W[1](G) ⊆ absConvexHull ℝ (Set.range a) := by
  let C : ConvexBody E := absConvexHull_range_body a
  intro y hy
  have hy_dual : ‖y‖[⟨G, hG⟩,*] ≤ 1 := by
    -- Reinterpret unit-ellipsoid membership through the dual norm of `G`.
    rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hG] at hy
  have hsingleton_subset :
      ({y} : Set E) ⊆ (C : Set E) := by
    refine subset_of_supportFunction_le_on_domain ({y} : Set E) (C : Set E)
      C.nonempty C.isClosed C.convex ?_
    intro x hxdom
    have hnorm_nonneg : 0 ≤ ‖x‖[⟨G, hG⟩] := by
      rw [positiveDefMatrixNorm_def ⟨G, hG⟩]
      exact Real.sqrt_nonneg _
    have hsupport_eq :
        C.supportFunctionReal x =
          maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x := by
      simpa [C, absConvexHull_range_body] using
        (supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a x)
    have hinner_le_support :
        inner ℝ y x ≤ C.supportFunctionReal x := by
      -- Compare the singleton contribution with the norm bound and then with the support value.
      calc
        inner ℝ y x ≤ ‖y‖[⟨G, hG⟩,*] * ‖x‖[⟨G, hG⟩] := by
            exact Seminorm.inner_le_dualNorm_mul (positiveDefMatrixNorm _ _) x y
        _ ≤ 1 * ‖x‖[⟨G, hG⟩] := by
              exact mul_le_mul_of_nonneg_right hy_dual hnorm_nonneg
        _ = ‖x‖[⟨G, hG⟩] := by ring
        _ ≤ maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) x := hnorm_le x
        _ = C.supportFunctionReal x := hsupport_eq.symm
    obtain ⟨s, hsC, hsMax⟩ := C.exists_isMaxOn_inner x
    have hs_support :
        C.supportFunctionReal x = inner ℝ s x := by
      have hs_lub :
          IsLUB ((fun t : E ↦ inner ℝ t x) '' (C : Set E)) (inner ℝ s x) := by
        simpa [isMaxOn_iff] using hsMax.isLUB hsC
      -- Replace the support value by a maximizing body point.
      rw [ConvexBody.supportFunctionReal_eq_sSup_inner]
      exact hs_lub.csSup_eq ⟨inner ℝ s x, ⟨s, hsC, rfl⟩⟩
    have hinner_le_s : inner ℝ y x ≤ inner ℝ s x := by
      simpa [hs_support] using hinner_le_support
    -- Compare the singleton support function with the body support by the maximizing witness.
    rw [supportFunction_apply, supportFunction_apply]
    have hsingleton :
        sSup ((fun g : E ↦ ((inner ℝ g x : ℝ) : EReal)) '' ({y} : Set E)) =
          ((inner ℝ y x : ℝ) : EReal) := by
      simp
    rw [hsingleton]
    calc
      ((inner ℝ y x : ℝ) : EReal) ≤ ((inner ℝ s x : ℝ) : EReal) := by
        exact_mod_cast hinner_le_s
      _ ≤ sSup ((fun t : E ↦ ((inner ℝ t x : ℝ) : EReal)) '' (C : Set E)) := by
        exact le_sSup ⟨s, hsC, rfl⟩
  have hy_mem : y ∈ (C : Set E) := hsingleton_subset (by simp)
  simpa [C, absConvexHull_range_body] using hy_mem

/-- Helper for Proposition 7.17: every simplex-weighted Gram matrix over the family `a₁, …, aₘ`
has its unit ellipsoid contained in `absConvexHull ℝ (Set.range a)`. -/
lemma weightedGramUnitEllipsoidSubsetAbsConvexHull
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ)))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (hrep : G = B[a](weights.weights)) :
    W[1](G) ⊆ absConvexHull ℝ (Set.range a) := by
  -- The weighted support-function bound is exactly the input needed for the generic containment
  -- lemma above.
  refine unitEllipsoid_subset_absConvexHull_of_norm_bound a hG ?_
  intro x
  exact weightedGramNorm_le_maxTypeObjective_absInner a weights hG hrep x

/-- Helper for Proposition 7.17: the unit ellipsoid of the initial Gram matrix already lies in
the canonical absolutely convex hull of the generators. -/
lemma initialUnitEllipsoid_subset_absConvexHull
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hGram : (centralSymmetryGramMatrix a).PosDef) :
    W[1]((centralSymmetryGramMatrix a)) ⊆ absConvexHull ℝ (Set.range a) := by
  -- This is the special case of the generic support-function argument at the initial Gram matrix.
  refine unitEllipsoid_subset_absConvexHull_of_norm_bound a hGram ?_
  intro x
  exact initialGramNorm_le_maxTypeObjective_absInner a hGram x

/-- Helper for Proposition 7.17: the initial Gram matrix already gives the centered
`sqrt m`-rounding of the canonical absolutely convex hull. -/
private lemma initialGramBetaRounding_sqrt_m
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hGram : (centralSymmetryGramMatrix a).PosDef) :
    IsBetaRounding
      (absConvexHull ℝ (Set.range a))
      (Real.sqrt (m : ℝ))
      (centralSymmetryGramMatrix a)
      (0 : E) := by
  refine ⟨?_, ?_⟩
  · -- Reuse the already proved unit-ellipsoid containment for the initial Gram matrix.
    simpa [centeredMatrixEllipsoid_one_eq_affineEllipsoid] using
      initialUnitEllipsoid_subset_absConvexHull a hGram
  · intro x hx
    let C : ConvexBody E := absConvexHull_range_body a
    have hx_body : x ∈ (C : Set E) := by
      simpa [C, absConvexHull_range_body] using hx
    rw [mem_matrixEllipsoid_iff_dualNorm_le hGram]
    refine csSup_le ?_ ?_
    · refine ⟨(0 : ℝ), (0 : E), ?_⟩
      constructor
      · -- The origin belongs to every seminorm closed ball of radius `1`.
        simpa [Seminorm.mem_closedBall_zero]
      · simp
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨s, hs_mem, hs_max⟩ := C.exists_isMaxOn_inner y
      have hs_support :
          C.supportFunctionReal y = inner ℝ s y := by
        have hs_lub :
            IsLUB ((fun t : E ↦ inner ℝ t y) '' (C : Set E)) (inner ℝ s y) := by
          simpa [isMaxOn_iff] using hs_max.isLUB hs_mem
        rw [ConvexBody.supportFunctionReal_eq_sSup_inner]
        exact hs_lub.csSup_eq ⟨inner ℝ s y, ⟨s, hs_mem, rfl⟩⟩
      have hsupport_le :
          inner ℝ x y ≤ C.supportFunctionReal y := by
        calc
          inner ℝ x y ≤ inner ℝ s y := hs_max hx_body
          _ = C.supportFunctionReal y := hs_support.symm
      have hsupport_eq :
          C.supportFunctionReal y =
            maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y := by
        simpa [C, absConvexHull_range_body] using
          (supportFunction_absConvexHull_range_toReal_eq_maxTypeObjective_absInner a y)
      have hy_norm :
          ‖y‖[⟨centralSymmetryGramMatrix a, hGram⟩] ≤ 1 := by
        -- Unpack the support-function witness back to the dual-norm unit ball constraint.
        simpa [Seminorm.mem_closedBall_zero] using hy
      calc
        (fun z : E ↦ inner ℝ (x - 0) z) y = inner ℝ x y := by simp
        _ ≤ C.supportFunctionReal y := hsupport_le
        _ = maxTypeObjective (fun i z ↦ |inner ℝ (a i) z|) y := hsupport_eq
        _ ≤ Real.sqrt (m : ℝ) * ‖y‖[⟨centralSymmetryGramMatrix a, hGram⟩] :=
              maxTypeObjective_absInner_le_sqrt_card_mul_initialGramNorm a hGram y
        _ ≤ Real.sqrt (m : ℝ) * 1 := by
              gcongr
        _ = Real.sqrt (m : ℝ) := by ring

/-- Helper for Proposition 7.17: a stage of the finite-family orbit packages the current
positive-definite matrix together with its simplex-weighted Gram representation. -/
private structure FiniteFamilyWeightedStage
    {m : ℕ+} (a : Fin (m : ℕ) → E) where
  matrix : Matrix (Fin n) (Fin n) ℝ
  posDef : matrix.PosDef
  weights : StdSimplex ℝ (Fin (m : ℕ))
  weightedGram_eq : matrix = B[a](weights.weights)

/-- Helper for Proposition 7.17: a rank-one update with coefficient `α ∈ [0, 1)` keeps a
positive-definite matrix positive definite. -/
private lemma centralSymmetricRoundingUpdatedMatrix_posDef
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) {g : E} {α : ℝ}
    (hα : α ∈ Set.Ico (0 : ℝ) 1) :
    (centralSymmetricRoundingUpdatedMatrix G g α).PosDef := by
  rcases hα with ⟨hα_nonneg, hα_lt_one⟩
  have hone_sub_pos : 0 < 1 - α := by
    linarith
  have hleft : ((1 - α) • G).PosDef := hG.smul hone_sub_pos
  have hbase : (Matrix.vecMulVec g g).PosSemidef := by
    simpa using Matrix.posSemidef_vecMulVec_self_star g
  have hright : (α • Matrix.vecMulVec g g).PosSemidef := hbase.smul hα_nonneg
  -- Rewrite the update into a positive-definite part plus a positive-semidefinite correction.
  rw [centralSymmetricRoundingUpdatedMatrix_eq]
  exact hleft.add_posSemidef hright

/-- Helper for Proposition 7.17: tracing `G⁻¹` against the rank-one matrix `aᵢ aᵢᵀ` recovers the
squared `G`-dual norm of `aᵢ`. -/
private lemma trace_inv_mul_vecMulVec_eq_dualNorm_sq
    {m : ℕ+} (a : Fin (m : ℕ) → E) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (i : Fin (m : ℕ)) :
    Matrix.trace (G⁻¹ * Matrix.vecMulVec (a i) (a i)) =
      ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
  have hinner_eq :
      inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)) =
        dotProduct (a i).ofLp ((G⁻¹).mulVec (a i).ofLp) := by
    -- Rewrite the Euclidean inner product through the coordinate dot product of `G⁻¹ aᵢ`.
    calc
      inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)) =
          dotProduct (a i).ofLp (((Matrix.toEuclideanLin G⁻¹) (a i)).ofLp) := by
            simpa [dotProduct_comm] using
              (EuclideanSpace.inner_eq_star_dotProduct (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)))
      _ = dotProduct (a i).ofLp ((G⁻¹).mulVec (a i).ofLp) := by
            rw [Matrix.toEuclideanLin_apply]
  -- Commute the trace, collapse the rank-one term, and rewrite the resulting quadratic form by
  -- the already-proved dual-norm identity.
  calc
    Matrix.trace (G⁻¹ * Matrix.vecMulVec (a i) (a i))
        = Matrix.trace (Matrix.vecMulVec (a i) (a i) * G⁻¹) := by
            simpa using (Matrix.trace_mul_comm G⁻¹ (Matrix.vecMulVec (a i) (a i)))
    _ = Matrix.trace (Matrix.vecMulVec (a i) (Matrix.vecMul (a i) G⁻¹)) := by
          rw [Matrix.vecMulVec_mul]
    _ = dotProduct (a i).ofLp (Matrix.vecMul (a i) G⁻¹) := by
          rw [Matrix.trace_vecMulVec]
    _ = dotProduct (a i).ofLp ((G⁻¹).mulVec (a i).ofLp) := by
          rw [dotProduct_comm]
          symm
          exact Matrix.dotProduct_mulVec (a i) G⁻¹ (a i)
    _ = inner ℝ (a i) ((Matrix.toEuclideanLin G⁻¹) (a i)) := by
          exact hinner_eq.symm
    _ = ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
          simpa [centralSymmetryScore] using
            (centralSymmetryScore_inv_eq_dualNorm_sq a hG i)

/-- Helper for Proposition 7.17: a simplex-weighted Gram representation forces the weighted sum
of the squared generator dual norms to equal the ambient dimension. -/
private lemma weightedGramDimEqSumDualNormSq
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ)))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef)
    (hrep : G = B[a](weights.weights)) :
    (n : ℝ) =
      ∑ i : Fin (m : ℕ), weights.weights i * ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
  have hInvMul : G⁻¹ * B[a](weights.weights) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    -- Substitute the weighted Gram representation and use the canonical inverse identity.
    rw [← hrep]
    let _ := hG.isUnit.invertible
    simpa using Matrix.inv_mul_of_invertible G
  have htrace := congrArg Matrix.trace hInvMul
  -- Trace the matrix identity, expand the weighted Gram matrix, and rewrite each rank-one term by
  -- the squared dual norm of the corresponding generator.
  calc
    (n : ℝ) = Matrix.trace (G⁻¹ * B[a](weights.weights)) := by
      simpa [Matrix.trace_one] using htrace.symm
    _ = ∑ i : Fin (m : ℕ),
          weights.weights i * Matrix.trace (G⁻¹ * Matrix.vecMulVec (a i) (a i)) := by
            simp [weightedGramMatrix, Matrix.mul_sum, Matrix.trace_smul]
    _ = ∑ i : Fin (m : ℕ), weights.weights i * ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [trace_inv_mul_vecMulVec_eq_dualNorm_sq a hG i]

/-- Helper for Proposition 7.17: every simplex-weighted Gram stage has radius at least `√n`. -/
private lemma weightedGramRadiusSq_ge_dim
    {m : ℕ+} (a : Fin (m : ℕ) → E) (weights : StdSimplex ℝ (Fin (m : ℕ)))
    {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef)
    (hrep : G = B[a](weights.weights)) :
    (n : ℝ) ≤
      (centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩) ^ (2 : ℕ) := by
  let r : ℝ := centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩
  have hr_nonneg : 0 ≤ r := by
    rw [show r =
      centralSymmetrySelectedRadius a G⁻¹ (scoreMaximizingIndex a G⁻¹) by
      exact centralSymmetricRoundingRadius_eq_scoreMaximizingIndex_selectedRadius a hG]
    exact Real.sqrt_nonneg _
  have hdual_le : ∀ i : Fin (m : ℕ), ‖a i‖[⟨G, hG⟩,*] ≤ r := by
    intro i
    have hmax_nonneg :
        0 ≤ ‖a (scoreMaximizingIndex a G⁻¹)‖[⟨G, hG⟩,*] := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩
        (a (scoreMaximizingIndex a G⁻¹))]
      exact Real.sqrt_nonneg _
    -- First compare to the chosen maximizing generator, then identify that generator norm with
    -- the owner-side radius of the body.
    calc
      ‖a i‖[⟨G, hG⟩,*] ≤ ‖a (scoreMaximizingIndex a G⁻¹)‖[⟨G, hG⟩,*] := by
            exact dualNorm_le_scoreMaximizingIndex a hG i
      _ = centralSymmetrySelectedRadius a G⁻¹ (scoreMaximizingIndex a G⁻¹) := by
            rw [centralSymmetrySelectedRadius,
              centralSymmetryScore_inv_eq_dualNorm_sq a hG (scoreMaximizingIndex a G⁻¹),
              Real.sqrt_sq_eq_abs, abs_of_nonneg hmax_nonneg]
      _ = r := by
            symm
            exact centralSymmetricRoundingRadius_eq_scoreMaximizingIndex_selectedRadius a hG
  have htrace :
      (n : ℝ) =
        ∑ i : Fin (m : ℕ), weights.weights i * ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) :=
    weightedGramDimEqSumDualNormSq a weights hG hrep
  have hweights_total : ∑ i : Fin (m : ℕ), weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using weights.total
  have hsum_le :
      (∑ i : Fin (m : ℕ), weights.weights i * ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ)) ≤
        ∑ i : Fin (m : ℕ), weights.weights i * r ^ (2 : ℕ) := by
    -- Bound every weighted summand by the common maximal dual radius `r`.
    refine Finset.sum_le_sum ?_
    intro i hi
    have hi_nonneg : 0 ≤ ‖a i‖[⟨G, hG⟩,*] := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv ⟨G, hG⟩ (a i)]
      exact Real.sqrt_nonneg _
    have hsq_le : ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) ≤ r ^ (2 : ℕ) := by
      nlinarith [hdual_le i, hi_nonneg, hr_nonneg]
    exact mul_le_mul_of_nonneg_left hsq_le (weights.nonneg i)
  calc
    (n : ℝ) = ∑ i : Fin (m : ℕ), weights.weights i * ‖a i‖[⟨G, hG⟩,*] ^ (2 : ℕ) := htrace
    _ ≤ ∑ i : Fin (m : ℕ), weights.weights i * r ^ (2 : ℕ) := hsum_le
    _ = (∑ i : Fin (m : ℕ), weights.weights i) * r ^ (2 : ℕ) := by
          rw [Finset.sum_mul]
    _ = r ^ (2 : ℕ) := by
          simp [hweights_total]

/-- Helper for Proposition 7.17: for simplex-weighted Gram stages in dimension `n ≥ 2`, the
owner-side update coefficient lies in `[0, 1)`. -/
private lemma centralSymmetricRoundingAlpha_mem_Ico_of_weightedGram
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hn2 : 2 ≤ n)
    (weights : StdSimplex ℝ (Fin (m : ℕ))) {G : Matrix (Fin n) (Fin n) ℝ}
    (hG : G.PosDef) (hrep : G = B[a](weights.weights)) :
    centralSymmetricRoundingAlpha (absConvexHull_range_body a) ⟨G, hG⟩ ∈ Set.Ico (0 : ℝ) 1 := by
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hsigma_nonneg :
      0 ≤
        (centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩) ^ (2 : ℕ) /
            (n : ℝ) -
          1 := by
    -- The weighted-Gram radius bound `n ≤ r²` is exactly the nonnegativity of the normalized
    -- scalar parameter `σ = r² / n - 1`.
    have hradius_sq_ge :
        (n : ℝ) ≤
          (centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩) ^ (2 : ℕ) :=
      weightedGramRadiusSq_ge_dim a weights hG hrep
    have hdiv :
        1 ≤
          (centralSymmetricRoundingRadius (absConvexHull_range_body a) ⟨G, hG⟩) ^ (2 : ℕ) /
            (n : ℝ) := by
      exact (le_div_iff₀ hn_pos).2 <| by simpa [mul_comm] using hradius_sq_ge
    linarith
  -- Route correction: keep the proof in the scalar owner normal form `α = α*(σ)` and import the
  -- weighted-Gram information only through the sign of `σ`.
  simpa [centralSymmetricRoundingAlpha] using
    (centralSymmetryRoundingAlphaStar_mem_Ico (n := n) hn2 hsigma_nonneg)

/-- Helper for Proposition 7.17: one recursive weighted-Gram stage advances by the canonical
rank-one update and keeps the explicit simplex-weight formula. -/
private lemma finiteFamilyWeightedStage_succ
    {m : ℕ+} (a : Fin (m : ℕ) → E) (hn2 : 2 ≤ n)
    (s : FiniteFamilyWeightedStage a) :
    ∃ s' : FiniteFamilyWeightedStage a,
      s'.matrix =
        centralSymmetricRoundingUpdatedMatrix s.matrix
          (a (scoreMaximizingIndex a s.matrix⁻¹))
          (centralSymmetricRoundingAlpha (absConvexHull_range_body a) ⟨s.matrix, s.posDef⟩) ∧
      (∀ i : Fin (m : ℕ),
        s'.weights.weights i =
          ((1 - centralSymmetricRoundingAlpha (absConvexHull_range_body a) ⟨s.matrix, s.posDef⟩) *
              s.weights.weights i +
            (Finsupp.single (scoreMaximizingIndex a s.matrix⁻¹)
              (centralSymmetricRoundingAlpha (absConvexHull_range_body a) ⟨s.matrix, s.posDef⟩)) i)) := by
  let j : Fin (m : ℕ) := scoreMaximizingIndex a s.matrix⁻¹
  let α : ℝ := centralSymmetricRoundingAlpha (absConvexHull_range_body a) ⟨s.matrix, s.posDef⟩
  have hα : α ∈ Set.Ico (0 : ℝ) 1 := by
    -- The stage already has a weighted-Gram presentation, so the owner coefficient is admissible.
    simpa [α] using
      centralSymmetricRoundingAlpha_mem_Ico_of_weightedGram a hn2 s.weights s.posDef
        s.weightedGram_eq
  let updatedWeights : Fin (m : ℕ) →₀ ℝ :=
    (1 - α) • s.weights.weights + Finsupp.single j α
  have hupdated_nonneg : ∀ i : Fin (m : ℕ), 0 ≤ updatedWeights i := by
    -- The explicit update remains inside the simplex because it is a convex combination.
    intro i
    have hone_sub_nonneg : 0 ≤ 1 - α := sub_nonneg.mpr hα.2.le
    by_cases hij : i = j
    · subst hij
      simpa [updatedWeights] using
        add_nonneg (mul_nonneg hone_sub_nonneg (s.weights.nonneg j)) hα.1
    · have hmul_nonneg : 0 ≤ (1 - α) * s.weights.weights i :=
        mul_nonneg hone_sub_nonneg (s.weights.nonneg i)
      simpa [updatedWeights, hij] using hmul_nonneg
  have hs_total : ∑ i : Fin (m : ℕ), s.weights.weights i = 1 := by
    simpa [Finsupp.sum_fintype] using s.weights.total
  have hupdated_total_fn : ∑ i : Fin (m : ℕ), updatedWeights i = 1 := by
    -- The updated coefficients still carry total mass `1`.
    calc
      ∑ i : Fin (m : ℕ), updatedWeights i
          = ∑ i : Fin (m : ℕ),
              ((1 - α) * s.weights.weights i + (Finsupp.single j α) i) := by
                simp [updatedWeights]
      _ = (1 - α) * ∑ i : Fin (m : ℕ), s.weights.weights i +
            ∑ i : Fin (m : ℕ), (Finsupp.single j α) i := by
              rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (1 - α) * 1 + α := by
            simp [hs_total, Finsupp.single_apply]
      _ = 1 := by ring
  have hupdated_total : updatedWeights.sum (fun i w ↦ w) = 1 := by
    simpa [Finsupp.sum_fintype] using hupdated_total_fn
  let weights' : StdSimplex ℝ (Fin (m : ℕ)) :=
    ⟨updatedWeights, hupdated_nonneg, hupdated_total⟩
  refine ⟨
    { matrix :=
        centralSymmetricRoundingUpdatedMatrix s.matrix (a j) α
      posDef := centralSymmetricRoundingUpdatedMatrix_posDef s.posDef hα
      weights := weights'
      weightedGram_eq := ?_ },
    rfl, ?_⟩
  · -- Expand both sides entrywise and fold the updated coefficients into the weighted Gram form.
    ext p q
    calc
      centralSymmetricRoundingUpdatedMatrix s.matrix (a j) α p q
          = (1 - α) * (∑ i : Fin (m : ℕ), s.weights.weights i * a i p * a i q) +
              α * (a j p * a j q) := by
                rw [s.weightedGram_eq, centralSymmetricRoundingUpdatedMatrix_eq]
                simp [weightedGramMatrix_apply, Matrix.add_apply, Matrix.smul_apply,
                  Matrix.vecMulVec_apply]
      _ = (1 - α) * (∑ i : Fin (m : ℕ), s.weights.weights i * a i p * a i q) +
            ∑ i : Fin (m : ℕ), (Finsupp.single j α) i * a i p * a i q := by
              congr 1
              calc
                α * (a j p * a j q) = α * a j p * a j q := by ring
                _ = ∑ i : Fin (m : ℕ), (Finsupp.single j α) i * a i p * a i q := by
                      simp [Finsupp.single_apply]
      _ = ∑ i : Fin (m : ℕ),
            ((1 - α) * (s.weights.weights i * a i p * a i q) +
              (Finsupp.single j α) i * a i p * a i q) := by
              rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      _ = ∑ i : Fin (m : ℕ),
            (((1 - α) * s.weights.weights i + (Finsupp.single j α) i) * a i p * a i q) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
      _ = ∑ i : Fin (m : ℕ), weights'.weights i * a i p * a i q := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [weights', updatedWeights]
      _ = B[a](weights'.weights) p q := by
            rw [weightedGramMatrix_apply]
  · -- The chosen simplex witness carries the explicit coordinate update by construction.
    intro i
    simp [weights', updatedWeights, α, j]

/-- Helper for Proposition 7.17: in the `2 ≤ n` branch, the finite-family chapter method can be
constructed as an unconditional recursive orbit on concrete simplex weights, and every stage
still has its unit ellipsoid in the canonical absolutely convex hull. -/
private theorem finiteFamilyMethodData_ofTwoLe
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn2 : 2 ≤ n) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ method : CentralSymmetricRoundingMethod n,
      ∃ weights : ℕ → StdSimplex ℝ (Fin (m : ℕ)),
      (method.body : Set E) = absConvexHull ℝ (Set.range a) ∧
      method.initialMatrix = centralSymmetryGramMatrix a ∧
      method.gamma = γ ∧
      (∀ k : ℕ, method k = B[a]((weights k).weights)) ∧
      (∀ i : Fin (m : ℕ), (weights 0).weights i = (m : ℝ)⁻¹) ∧
      (∀ k : ℕ, ∀ i : Fin (m : ℕ), 0 < (weights k).weights i) ∧
      (∀ k : ℕ, ∀ i : Fin (m : ℕ),
        (weights (k + 1)).weights i =
          ((1 - method.alpha k) * (weights k).weights i +
            (Finsupp.single (scoreMaximizingIndex a ((method k)⁻¹)) (method.alpha k)) i)) ∧
      (∀ k : ℕ,
        centeredMatrixEllipsoid (method k) 1 ⊆ (method.body : Set E)) := by
  classical
  let c : ℝ := (m : ℝ)⁻¹
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.2
  let weights0 : StdSimplex ℝ (Fin (m : ℕ)) :=
    ⟨Finsupp.equivFunOnFinite.symm (fun _ : Fin (m : ℕ) ↦ c),
      by
        intro i
        exact le_of_lt (by simpa [c] using inv_pos.mpr hm_pos),
      by
        have hsum_fun : ∑ i : Fin (m : ℕ), c = 1 := by
          have hm_ne : (m : ℝ) ≠ 0 := ne_of_gt hm_pos
          simpa [c, hm_ne] using
            (show (∑ _ : Fin (m : ℕ), c) = (m : ℝ) * c by simp [c])
        simpa [c] using (Finsupp.equivFunOnFinite_symm_sum (fun _ : Fin (m : ℕ) ↦ c)).trans
          hsum_fun⟩
  have hweights0_apply : ∀ i : Fin (m : ℕ), weights0.weights i = c := by
    intro i
    simp [weights0, c]
  have hweightedGram0 : centralSymmetryGramMatrix a = B[a](weights0.weights) := by
    -- The initial Gram matrix is exactly the weighted Gram operator for the uniform simplex point.
    ext p q
    rw [centralSymmetryGramMatrix, weightedGramMatrix_apply, Matrix.smul_apply, Matrix.sum_apply]
    change
      (m : ℝ)⁻¹ * ∑ i : Fin (m : ℕ), (a i).ofLp p * (a i).ofLp q =
        ∑ i : Fin (m : ℕ), weights0.weights i * (a i).ofLp p * (a i).ofLp q
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hweights0_apply i]
    ring
  let stage0 : FiniteFamilyWeightedStage a :=
    { matrix := centralSymmetryGramMatrix a
      posDef := hGram
      weights := weights0
      weightedGram_eq := hweightedGram0 }
  let stage : ℕ → FiniteFamilyWeightedStage a :=
    Nat.rec stage0 fun _ s ↦ Classical.choose (finiteFamilyWeightedStage_succ a hn2 s)
  have hstage_succ :
      ∀ k : ℕ,
        (stage (k + 1)).matrix =
            centralSymmetricRoundingUpdatedMatrix (stage k).matrix
              (a (scoreMaximizingIndex a ((stage k).matrix)⁻¹))
              (centralSymmetricRoundingAlpha (absConvexHull_range_body a)
                ⟨(stage k).matrix, (stage k).posDef⟩) ∧
          (∀ i : Fin (m : ℕ),
            (stage (k + 1)).weights.weights i =
              ((1 - centralSymmetricRoundingAlpha (absConvexHull_range_body a)
                    ⟨(stage k).matrix, (stage k).posDef⟩) *
                  (stage k).weights.weights i +
                (Finsupp.single (scoreMaximizingIndex a ((stage k).matrix)⁻¹)
                  (centralSymmetricRoundingAlpha (absConvexHull_range_body a)
                    ⟨(stage k).matrix, (stage k).posDef⟩)) i)) := by
    intro k
    -- Unfold one recursive step and reuse the successor-stage specification proved above.
    simpa [stage] using
      (Classical.choose_spec (finiteFamilyWeightedStage_succ a hn2 (stage k)))
  let method : CentralSymmetricRoundingMethod n :=
    { one_le_dim := by omega
      body := absConvexHull_range_body a
      body_balanced := absConvexHull_range_body_balanced a
      gamma := γ
      one_lt_gamma := hγ
      initialMatrix := centralSymmetryGramMatrix a
      matrix := fun k ↦ (stage k).matrix
      maximizer := fun k ↦ a (scoreMaximizingIndex a ((stage k).matrix)⁻¹)
      matrix_posDef := fun k ↦ (stage k).posDef
      matrix_zero := rfl
      maximizer_isMaxOn := by
        intro k
        -- Each recursive stage chooses the canonical score maximizer for its current matrix.
        simpa [absConvexHull_range_body] using
          scoreMaximizingIndex_isMaxOn_absConvexHull_dualNorm
            (a := a) (G := (stage k).matrix) ((stage k).posDef)
      matrix_succ_of_gt_threshold := by
        intro k
        dsimp
        intro _
        exact (hstage_succ k).1 }
  let weights : ℕ → StdSimplex ℝ (Fin (m : ℕ)) := fun k ↦ (stage k).weights
  refine ⟨method, weights, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · -- The recursive stage package keeps the weighted-Gram identity at every time.
    intro k
    exact (stage k).weightedGram_eq
  · -- Time `0` starts from the uniform simplex weights.
    intro i
    change weights0.weights i = (m : ℝ)⁻¹
    simpa [weights0, c] using hweights0_apply i
  · intro k i
    induction k with
    | zero =>
        -- The uniform simplex weights are strictly positive.
        change 0 < weights0.weights i
        simpa [weights0, c] using inv_pos.mpr hm_pos
    | succ k ih =>
        let α : ℝ :=
          centralSymmetricRoundingAlpha (absConvexHull_range_body a)
            ⟨(stage k).matrix, (stage k).posDef⟩
        let j : Fin (m : ℕ) := scoreMaximizingIndex a ((stage k).matrix)⁻¹
        have hα : α ∈ Set.Ico (0 : ℝ) 1 := by
          -- The current weighted-Gram stage again gives an admissible update coefficient.
          simpa [α] using
            centralSymmetricRoundingAlpha_mem_Ico_of_weightedGram a hn2 (stage k).weights
              (stage k).posDef (stage k).weightedGram_eq
        have hformula := (hstage_succ k).2 i
        rw [hformula]
        by_cases hij : i = j
        · subst hij
          have hmain_pos : 0 < (1 - α) * (stage k).weights.weights j := by
            exact mul_pos (sub_pos.mpr hα.2) ih
          have : 0 < (1 - α) * (stage k).weights.weights j + α := by
            linarith [hmain_pos, hα.1]
          simpa [α, j, Finsupp.single_apply] using this
        · have hmain_pos : 0 < (1 - α) * (stage k).weights.weights i := by
            exact mul_pos (sub_pos.mpr hα.2) ih
          simpa [α, j, Finsupp.single_apply, hij] using hmain_pos
  · -- The recursive stage constructor already records the explicit simplex update.
    intro k i
    simpa [method, weights, CentralSymmetricRoundingMethod.alpha_eq] using (hstage_succ k).2 i
  · intro k
    -- Every weighted-Gram stage keeps its unit ellipsoid inside the canonical absolutely convex hull.
    simpa [method, weights, absConvexHull_range_body] using
      weightedGramUnitEllipsoidSubsetAbsConvexHull
        (a := a) (weights k) ((stage k).posDef) ((stage k).weightedGram_eq)

/-- Helper for Proposition 7.17: forgetting the explicit recursive weight data recovers the
lighter finite-family method surface used by the main existence theorem. -/
private theorem finiteFamilyMethod_exists_of_two_le
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn2 : 2 ≤ n) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ method : CentralSymmetricRoundingMethod n,
      (method.body : Set E) = absConvexHull ℝ (Set.range a) ∧
      method.initialMatrix = centralSymmetryGramMatrix a ∧
      method.gamma = γ ∧
      (∀ k : ℕ, ∃ weightsk : StdSimplex ℝ (Fin (m : ℕ)),
        method k = B[a](weightsk.weights)) ∧
      (∀ k : ℕ,
        centeredMatrixEllipsoid (method k) 1 ⊆ (method.body : Set E)) := by
  rcases finiteFamilyMethodData_ofTwoLe a hn2 hγ hGram with
    ⟨method, weights, hbody, hinit, hgamma_eq, hstage, _hweights0, _hpos, _hsucc, hinner_all⟩
  refine ⟨method, hbody, hinit, hgamma_eq, ?_, hinner_all⟩
  intro k
  exact ⟨weights k, hstage k⟩

/-- Helper for Proposition 7.17: every genuinely continuing step gains at least
`((γ - 1)^2) / γ^2` in logarithmic determinant. -/
private lemma logDetIncrement_ge_uniformDrop_of_not_stopping
    {γ : ℝ} (method : CentralSymmetricRoundingMethod n)
    (hn2 : 2 ≤ n) (hgamma_eq : method.gamma = γ) (hγ : 1 < γ) {k : ℕ}
    (hk : ¬ method.stoppingCriterion k) :
    (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ) ≤
      Real.log (Matrix.det (method (k + 1))) - Real.log (Matrix.det (method k)) := by
  let σ : ℝ := rankOneUpdateSigma (method k) (method.matrix_posDef k) (method.maximizer k)
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hcontinue : γ * Real.sqrt (n : ℝ) < method.radius k := by
    -- A genuinely continuing step lies strictly above the owner-side stopping threshold.
    rw [CentralSymmetricRoundingMethod.stoppingCriterion, hgamma_eq] at hk
    exact lt_of_not_ge hk
  have hradius_eq :
      method.radius k =
        ‖method.maximizer k‖[⟨method k, method.matrix_posDef k⟩,*] := by
    let G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef} := ⟨method k, method.matrix_posDef k⟩
    rcases method.maximizer_isMaxOn k with ⟨hk_mem, hk_max⟩
    have hk_lub :
        IsLUB
          ((fun g : E ↦ ‖g‖[G,*]) '' ((method.body : ConvexBody E) : Set E))
          ‖method.maximizer k‖[G,*] := by
      simpa [G, isMaxOn_iff] using hk_max.isLUB hk_mem
    rw [CentralSymmetricRoundingMethod.radius_eq, centralSymmetricRoundingRadius_eq_sSup]
    exact hk_lub.csSup_eq
      ⟨‖method.maximizer k‖[G,*], ⟨method.maximizer k, hk_mem, rfl⟩⟩
  have hmatrix_succ :
      method (k + 1) =
        centralSymmetricRoundingUpdatedMatrix (method k) (method.maximizer k) (method.alpha k) := by
    -- Rewrite the next iterate through the canonical rank-one update.
    have hcontinue' :
        method.gamma * Real.sqrt (n : ℝ) <
          centralSymmetricRoundingRadius method.body ⟨method.matrix k, method.matrix_posDef k⟩ := by
      simpa [CentralSymmetricRoundingMethod.radius_eq, hgamma_eq] using hcontinue
    simpa [CentralSymmetricRoundingMethod.alpha_eq, CentralSymmetricRoundingMethod.radius_eq] using
      method.matrix_succ_of_gt_threshold k hcontinue'
  have hsigma_eq :
      σ = method.radius k ^ (2 : ℕ) / (n : ℝ) - 1 := by
    -- The rank-one potential uses the same normalized squared radius as the owner method.
    dsimp [σ]
    rw [rankOneUpdateSigma_def, ← hradius_eq]
  have hsigma_pos : 0 < σ := by
    -- Continuing steps satisfy `σ ≥ γ² - 1 > 0`.
    have hsq : γ ^ (2 : ℕ) * (n : ℝ) < method.radius k ^ (2 : ℕ) := by
      have hgamma_nonneg : 0 ≤ γ := by linarith
      have hr_nonneg : 0 ≤ method.radius k := by
        rw [hradius_eq, positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        exact Real.sqrt_nonneg _
      have hleft_nonneg : 0 ≤ γ * Real.sqrt (n : ℝ) := by positivity
      have habs :
          |γ * Real.sqrt (n : ℝ)| < |method.radius k| := by
        simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hr_nonneg] using hcontinue
      have hsq' : (γ * Real.sqrt (n : ℝ)) ^ (2 : ℕ) < method.radius k ^ (2 : ℕ) :=
        (sq_lt_sq).2 habs
      simpa [pow_two, Real.sq_sqrt hn_pos.le, mul_assoc, mul_left_comm, mul_comm] using hsq'
    have hdiv : γ ^ (2 : ℕ) < method.radius k ^ (2 : ℕ) / (n : ℝ) := by
      exact (lt_div_iff₀ hn_pos).2 <| by
        simpa [mul_assoc, mul_left_comm, mul_comm] using hsq
    have hγ_gap : 0 < γ ^ (2 : ℕ) - 1 := by
      nlinarith
    rw [hsigma_eq]
    linarith
  have halpha_eq :
      method.alpha k =
        rankOneUpdateOptimalAlpha (method k) (method.matrix_posDef k) (method.maximizer k) := by
    -- The method coefficient is exactly the optimal rank-one update coefficient.
    simpa [rankOneUpdateOptimalAlpha, CentralSymmetricRoundingMethod.alpha_eq,
      centralSymmetricRoundingAlpha] using
      congrArg (centralSymmetryRoundingAlphaStar n) hsigma_eq.symm
  have hα_mem :
      method.alpha k ∈ Set.Ico (0 : ℝ) 1 := by
    -- The optimal coefficient lies in the admissible interval on continuing steps.
    rw [halpha_eq]
    exact rankOneUpdateOptimalAlpha_mem_Ico (method k) (method.matrix_posDef k)
      (method.maximizer k) hn2 hsigma_pos
  have hratio_eq :
      rankOneUpdatePotential (method k) (method.matrix_posDef k) (method.maximizer k)
          (method.alpha k) =
        Real.log (Matrix.det (method (k + 1)) / Matrix.det (method k)) := by
    -- Lemma 7.4 identifies the potential with the determinant ratio of the update.
    simpa [halpha_eq, hmatrix_succ, rankOneUpdatedMatrix, centralSymmetricRoundingUpdatedMatrix] using
      (rankOneUpdatePotential_eq_log_det_ratio (method k) (method.matrix_posDef k)
        (method.maximizer k)
        (rankOneUpdateOptimalAlpha_mem_Ico (method k) (method.matrix_posDef k)
          (method.maximizer k) hn2 hsigma_pos))
  have hgap_log :
      Real.log (1 + σ) - σ / (1 + σ) ≤
        rankOneUpdatePotential (method k) (method.matrix_posDef k) (method.maximizer k)
          (method.alpha k) := by
    -- The optimal rank-one potential dominates the scalar lower bound from Lemma 7.4.
    rw [halpha_eq]
    exact rankOneUpdatePotential_optimalAlpha_lower_bound_log
      (method k) (method.matrix_posDef k) (method.maximizer k) hn2 hsigma_pos
  have hboundary :
      2 * Real.log γ - (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) ≤
        Real.log (1 + σ) - σ / (1 + σ) := by
    have hγ_pos : 0 < γ := lt_trans zero_lt_one hγ
    have hγ_sq_pos : 0 < γ ^ (2 : ℕ) := by positivity
    have hγ_sq_le : γ ^ (2 : ℕ) ≤ 1 + σ := by
      rw [hsigma_eq]
      have hsq : γ ^ (2 : ℕ) * (n : ℝ) < method.radius k ^ (2 : ℕ) := by
        have hgamma_nonneg : 0 ≤ γ := by linarith
        have hr_nonneg : 0 ≤ method.radius k := by
          rw [hradius_eq, positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
          exact Real.sqrt_nonneg _
        have hleft_nonneg : 0 ≤ γ * Real.sqrt (n : ℝ) := by positivity
        have habs :
            |γ * Real.sqrt (n : ℝ)| < |method.radius k| := by
          simpa [abs_of_nonneg hleft_nonneg, abs_of_nonneg hr_nonneg] using hcontinue
        have hsq' : (γ * Real.sqrt (n : ℝ)) ^ (2 : ℕ) < method.radius k ^ (2 : ℕ) :=
          (sq_lt_sq).2 habs
        simpa [pow_two, Real.sq_sqrt hn_pos.le, mul_assoc, mul_left_comm, mul_comm] using hsq'
      have hdiv : γ ^ (2 : ℕ) < method.radius k ^ (2 : ℕ) / (n : ℝ) := by
        exact (lt_div_iff₀ hn_pos).2 <| by
          simpa [mul_assoc, mul_left_comm, mul_comm] using hsq
      linarith
    have hone_sigma_pos : 0 < 1 + σ := by
      linarith
    have hratio_pos : 0 < (1 + σ) / γ ^ (2 : ℕ) := div_pos hone_sigma_pos hγ_sq_pos
    have hlog_ratio :
        1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹ ≤ Real.log ((1 + σ) / γ ^ (2 : ℕ)) :=
      Real.one_sub_inv_le_log_of_pos hratio_pos
    have hgap_le_log_ratio :
        1 / γ ^ (2 : ℕ) - 1 / (1 + σ) ≤
          Real.log ((1 + σ) / γ ^ (2 : ℕ)) := by
      have hcoeff_le_one : (γ ^ (2 : ℕ))⁻¹ ≤ 1 := by
        have hgamma_sq_ge_one : 1 ≤ γ ^ (2 : ℕ) := by nlinarith
        simpa using
          (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by positivity) hgamma_sq_ge_one)
      have hratio_ge_one : 1 ≤ (1 + σ) / γ ^ (2 : ℕ) := by
        exact (le_div_iff₀ hγ_sq_pos).2 <| by simpa using hγ_sq_le
      have hcore_nonneg : 0 ≤ 1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹ := by
        have hratio_inv_le : ((1 + σ) / γ ^ (2 : ℕ))⁻¹ ≤ 1 := by
          simpa [one_div] using
            (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by positivity) hratio_ge_one)
        exact sub_nonneg.mpr hratio_inv_le
      have hscaled :
          (γ ^ (2 : ℕ))⁻¹ * (1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹) ≤
            1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹ := by
        have hscaled' := mul_le_mul_of_nonneg_right hcoeff_le_one hcore_nonneg
        simpa [mul_comm, mul_left_comm, mul_assoc] using hscaled'
      have hrewrite :
          1 / γ ^ (2 : ℕ) - 1 / (1 + σ) =
            (γ ^ (2 : ℕ))⁻¹ * (1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹) := by
        field_simp [hγ_sq_pos.ne', hone_sigma_pos.ne']
      calc
        1 / γ ^ (2 : ℕ) - 1 / (1 + σ)
            = (γ ^ (2 : ℕ))⁻¹ * (1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹) := hrewrite
        _ ≤ 1 - ((1 + σ) / γ ^ (2 : ℕ))⁻¹ := hscaled
        _ ≤ Real.log ((1 + σ) / γ ^ (2 : ℕ)) := hlog_ratio
    have hlog_div :
        Real.log ((1 + σ) / γ ^ (2 : ℕ)) =
          Real.log (1 + σ) - Real.log (γ ^ (2 : ℕ)) := by
      exact Real.log_div (ne_of_gt hone_sigma_pos) (pow_ne_zero _ (ne_of_gt hγ_pos))
    have hgamma_log :
        Real.log (γ ^ (2 : ℕ)) = 2 * Real.log γ := by
      rw [pow_two, Real.log_mul hγ_pos.ne' hγ_pos.ne']
      ring
    have hmain :
        Real.log (γ ^ (2 : ℕ)) - 1 + 1 / γ ^ (2 : ℕ) ≤
          Real.log (1 + σ) - 1 + 1 / (1 + σ) := by
      calc
        Real.log (γ ^ (2 : ℕ)) - 1 + 1 / γ ^ (2 : ℕ)
            ≤ Real.log (γ ^ (2 : ℕ)) - 1 + 1 / (1 + σ) +
                Real.log ((1 + σ) / γ ^ (2 : ℕ)) := by
                  linarith [hgap_le_log_ratio]
        _ = Real.log (1 + σ) - 1 + 1 / (1 + σ) := by
              rw [hlog_div]
              ring
    calc
      2 * Real.log γ - (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ)
          = Real.log (γ ^ (2 : ℕ)) - 1 + 1 / γ ^ (2 : ℕ) := by
              rw [hgamma_log]
              field_simp [ne_of_gt hγ_pos]
              ring
      _ ≤ Real.log (1 + σ) - 1 + 1 / (1 + σ) := hmain
      _ = Real.log (1 + σ) - σ / (1 + σ) := by
            field_simp [ne_of_gt hone_sigma_pos]
            ring
  have hdetk_pos : 0 < Matrix.det (method k) := (method.matrix_posDef k).det_pos
  have hdetk1_pos : 0 < Matrix.det (method (k + 1)) := (method.matrix_posDef (k + 1)).det_pos
  have hratio_log :
      Real.log (Matrix.det (method (k + 1)) / Matrix.det (method k)) =
        Real.log (Matrix.det (method (k + 1))) - Real.log (Matrix.det (method k)) := by
    exact Real.log_div hdetk1_pos.ne' hdetk_pos.ne'
  -- Compare the boundary scalar gain with the determinant ratio and then rewrite the ratio as a
  -- log-determinant increment.
  calc
    (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ)
        ≤ 2 * Real.log γ - (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
            exact CentralSymmetricRoundingMethod.gamma_step_gain_lower_bound hγ
    _ ≤ Real.log (1 + σ) - σ / (1 + σ) := hboundary
    _ ≤ rankOneUpdatePotential (method k) (method.matrix_posDef k) (method.maximizer k)
          (method.alpha k) := hgap_log
    _ = Real.log (Matrix.det (method (k + 1)) / Matrix.det (method k)) := hratio_eq
    _ = Real.log (Matrix.det (method (k + 1))) - Real.log (Matrix.det (method k)) := hratio_log

/-- Helper for Proposition 7.17: the initial `√m`-rounding and the persistent unit-ellipsoid
containment force the average logarithmic determinant gain to stay below `log m`. -/
private lemma avgLogDetGain_le_log_card_of_initialRounding
    {m : ℕ+} (method : CentralSymmetricRoundingMethod n) (hn2 : 2 ≤ n)
    (hInitial : IsBetaRounding (method.body : Set E) (Real.sqrt (m : ℝ)) (method 0) (0 : E))
    {T : ℕ} (hinner : centeredMatrixEllipsoid (method T) 1 ⊆ (method.body : Set E)) :
    (Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0))) / (n : ℝ) ≤
      Real.log (m : ℝ) := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.2
  have hn_pos_nat : 0 < n := by omega
  have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
  have hupper :
      Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0)) ≤
        2 * (n : ℝ) * Real.log (Real.sqrt (m : ℝ)) := by
    -- Theorem 7.6 gives the global log-det budget from the initial `√m`-rounding.
    exact
      CentralSymmetricRoundingMethod.terminal_logdet_upper_bound_of_rounding_containment
        (method := method) (R := Real.sqrt (m : ℝ)) (T := T) hInitial hinner
  have hupper' :
      Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0)) ≤
        (n : ℝ) * Real.log (m : ℝ) := by
    rw [Real.log_sqrt hm_pos.le] at hupper
    linarith
  have hdiv :
      (Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0))) / (n : ℝ) ≤
        ((n : ℝ) * Real.log (m : ℝ)) / (n : ℝ) := by
    field_simp [hn_pos.ne']
    linarith
  simpa [hn_pos.ne'] using hdiv

/-- Helper for Proposition 7.17: a stopping witness before `⌊B⌋` induces a canonical
termination witness whose first stopping index is still bounded by `B`. -/
private lemma termination_with_stoppingIndex_le_of_exists_stoppingCriterion_floor
    {B : ℝ} {method : CentralSymmetricRoundingMethod n} (hB_nonneg : 0 ≤ B)
    (hexists : ∃ k ≤ Nat.floor B, method.stoppingCriterion k) :
    ∃ hTerminate : method.Terminates,
      ((method.stoppingIndex hTerminate : ℝ) ≤ B) := by
  rcases hexists with ⟨k, hk_floor, hk_stop⟩
  let hTerminate : method.Terminates := ⟨k, hk_stop⟩
  refine ⟨hTerminate, ?_⟩
  have hleast : method.stoppingIndex hTerminate ≤ k :=
    (method.stoppingIndex_isLeast hTerminate).2 hk_stop
  have hfloor : method.stoppingIndex hTerminate ≤ Nat.floor B :=
    le_trans hleast hk_floor
  exact le_trans (by exact_mod_cast hfloor) (Nat.floor_le hB_nonneg)

/-- Helper for Proposition 7.17: the displayed stopping-index budget is nonnegative whenever
`γ > 1`. -/
private lemma maxAbsLinearSubdifferentialRoundingStoppingIndexBound_nonneg
    {m : ℕ+} {γ : ℝ} (hγ : 1 < γ) :
    0 ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
  unfold maxAbsLinearSubdifferentialRoundingStoppingIndexBound
  have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast m.2)
  have hgamma_sub_pos : 0 < γ - 1 := sub_pos.mpr hγ
  positivity

/-- Helper for Proposition 7.17: in dimension `1`, the owner-side update coefficient is always
either `0` or `1`. -/
private lemma centralSymmetricRoundingAlpha_eq_zero_or_one_of_dim_one
    (C : ConvexBody E) {G : Matrix (Fin n) (Fin n) ℝ} (hG : G.PosDef) (hn1 : n = 1) :
    let α := centralSymmetricRoundingAlpha C ⟨G, hG⟩
    α = 0 ∨ α = 1 := by
  subst hn1
  have halpha_eq :
      centralSymmetricRoundingAlpha C ⟨G, hG⟩ =
        ((centralSymmetricRoundingRadius C ⟨G, hG⟩) ^ (2 : ℕ) - 1) /
          ((1 : ℝ) * ((centralSymmetricRoundingRadius C ⟨G, hG⟩) ^ (2 : ℕ) - 1)) := by
    simpa using centralSymmetricRoundingAlpha_eq (n := 1) C ⟨G, hG⟩ (by norm_num)
  by_cases hr :
      (centralSymmetricRoundingRadius C ⟨G, hG⟩) ^ (2 : ℕ) - 1 = 0
  · -- On the boundary case `r² = 1`, the scalar-owner division convention gives `α = 0`.
    left
    rw [halpha_eq]
    simp [hr]
  · -- Off the boundary case, the one-dimensional formula simplifies to `(r² - 1)/(r² - 1) = 1`.
    right
    rw [halpha_eq]
    field_simp [hr]

/-- Helper for Proposition 7.17: in dimension `1`, a nonzero rank-one matrix `ggᵀ` is already
positive definite. -/
private lemma vecMulVec_posDef_of_ne_zero_dim_one
    (hn1 : n = 1) {g : E} (hg : g ≠ 0) :
    (Matrix.vecMulVec g g).PosDef := by
  subst hn1
  have hsemidef : (Matrix.vecMulVec g g).PosSemidef := by
    -- The rank-one matrix `ggᵀ` is always positive semidefinite.
    simpa using Matrix.posSemidef_vecMulVec_self_star g
  refine (Matrix.PosSemidef.posDef_iff_isUnit hsemidef).2 ?_
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_fin_one]
  apply isUnit_iff_ne_zero.mpr
  have hg0 : g 0 ≠ 0 := by
    -- In `Fin 1`, a nonzero vector has a nonzero unique coordinate.
    intro hg0
    apply hg
    ext i
    fin_cases i
    simpa using hg0
  simpa [Matrix.vecMulVec_apply] using mul_ne_zero hg0 hg0

/-- Helper for Proposition 7.17: in dimension `1`, the squared dual norm is the coordinate square
divided by the determinant. -/
private lemma dualNorm_sq_eq_coordinate_sq_div_det_of_dim_one
    {G : Matrix (Fin 1) (Fin 1) ℝ} (hG : G.PosDef) (x : EuclideanSpace ℝ (Fin 1)) :
    ‖x‖[⟨G, hG⟩,*] ^ (2 : ℕ) = (x.ofLp 0) ^ (2 : ℕ) / Matrix.det G := by
  have hdet_pos : 0 < Matrix.det G := hG.det_pos
  have hquad_nonneg :
      0 ≤ inner ℝ x ((Matrix.toEuclideanLin G⁻¹) x) := by
    -- Positive definiteness of `G⁻¹` makes the defining quadratic form nonnegative.
    have hPosLin : (Matrix.toEuclideanLin G⁻¹).IsPositive := by
      exact Matrix.isPositive_toEuclideanLin_iff.mpr hG.inv.posSemidef
    simpa [real_inner_comm] using hPosLin.inner_nonneg_right x
  have hlin :
      (((Matrix.toEuclideanLin G⁻¹) x).ofLp 0) = (Matrix.det G)⁻¹ * x.ofLp 0 := by
    -- In `Fin 1`, the inverse matrix acts by scalar multiplication with `det(G)⁻¹`.
    change Matrix.mulVec G⁻¹ x.ofLp 0 = (Matrix.det G)⁻¹ * x.ofLp 0
    rw [Matrix.inv_subsingleton, Matrix.mulVec_diagonal, Matrix.det_fin_one]
    simp [Ring.inverse_eq_inv]
  have hinner :
      inner ℝ x ((Matrix.toEuclideanLin G⁻¹) x) =
        ((x.ofLp 0) ^ (2 : ℕ)) / Matrix.det G := by
    -- Rewrite the inverse quadratic form through the unique coordinate of `x`.
    calc
      inner ℝ x ((Matrix.toEuclideanLin G⁻¹) x) =
          dotProduct (((Matrix.toEuclideanLin G⁻¹) x).ofLp) x.ofLp := by
            simpa using
              (EuclideanSpace.inner_eq_star_dotProduct x
                ((Matrix.toEuclideanLin G⁻¹) x))
      _ = dotProduct x.ofLp (((Matrix.toEuclideanLin G⁻¹) x).ofLp) := by
            rw [dotProduct_comm]
      _ = x.ofLp 0 * (((Matrix.toEuclideanLin G⁻¹) x).ofLp 0) := by
            simp [dotProduct]
      _ = x.ofLp 0 * ((Matrix.det G)⁻¹ * x.ofLp 0) := by
            rw [hlin]
      _ = ((x.ofLp 0) ^ (2 : ℕ)) / Matrix.det G := by
            field_simp [hdet_pos.ne']
  -- Route correction: push the dual norm down to the inverse quadratic form before using the
  -- one-dimensional matrix inverse formula.
  calc
    ‖x‖[⟨G, hG⟩,*] ^ (2 : ℕ) = inner ℝ x ((Matrix.toEuclideanLin G⁻¹) x) := by
      rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv, Real.sq_sqrt hquad_nonneg]
    _ = (x.ofLp 0) ^ (2 : ℕ) / Matrix.det G := hinner

/-- Helper for Proposition 7.17: once `γ < sqrt m`, the displayed stopping-index bound already
dominates `1`. -/
private lemma one_le_stoppingBound_of_lt_sqrt_card
    {m : ℕ+} {γ : ℝ} (hγ : 1 < γ) (hγ_lt : γ < Real.sqrt (m : ℝ)) :
    1 ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
  have hm_pos : 0 < (m : ℝ) := by
    exact_mod_cast m.2
  have hgamma_pos : 0 < γ := lt_trans zero_lt_one hγ
  have hgamma_ne : γ ≠ 0 := hgamma_pos.ne'
  have hgamma_sub_ne : γ - 1 ≠ 0 := by linarith
  have hgamma_sq_lt_m : γ ^ (2 : ℕ) < (m : ℝ) := by
    -- Squaring `γ < √m` is safe because both sides are nonnegative.
    have hsqrt_nonneg : 0 ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
    nlinarith [hγ_lt, Real.sq_sqrt hm_pos.le]
  have hlog_gamma_sq_lt :
      Real.log (γ ^ (2 : ℕ)) < Real.log (m : ℝ) := by
    exact Real.log_lt_log (by positivity) hgamma_sq_lt_m
  have hlog_gamma_sq :
      Real.log (γ ^ (2 : ℕ)) = 2 * Real.log γ := by
    rw [pow_two, Real.log_mul hgamma_ne hgamma_ne]
    ring
  have htwo_log_gamma_lt : 2 * Real.log γ < Real.log (m : ℝ) := by
    simpa [hlog_gamma_sq] using hlog_gamma_sq_lt
  have hgamma_budget :
      (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ) ≤ 2 * Real.log γ := by
    have hstep :=
      CentralSymmetricRoundingMethod.gamma_step_gain_lower_bound hγ
    have hdrop_nonneg : 0 ≤ (γ ^ (2 : ℕ) - 1) / γ ^ (2 : ℕ) := by
      have hgamma_sq_ge_one : 1 ≤ γ ^ (2 : ℕ) := by
        nlinarith
      exact div_nonneg (by nlinarith) (by positivity)
    linarith
  have hbase :
      (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ) ≤ Real.log (m : ℝ) := by
    linarith
  unfold maxAbsLinearSubdifferentialRoundingStoppingIndexBound
  have hscaled :=
    mul_le_mul_of_nonneg_left hbase (by positivity : 0 ≤ γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ))
  calc
    1 = (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * ((γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ)) := by
          field_simp [hgamma_ne, hgamma_sub_ne]
    _ ≤ (γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)) * Real.log (m : ℝ) := hscaled

/-- Helper for Proposition 7.17: in dimension `1`, the initial score-maximizing generator has the
largest coordinate square among the generators. -/
private lemma coordinateSq_le_scoreMaximizingIndex_of_dimOne
    {m : ℕ+} (a : Fin (m : ℕ) → EuclideanSpace ℝ (Fin 1))
    {G : Matrix (Fin 1) (Fin 1) ℝ} (hG : G.PosDef) (j : Fin (m : ℕ)) :
    (a j).ofLp 0 ^ (2 : ℕ) ≤
      (a (scoreMaximizingIndex a G⁻¹)).ofLp 0 ^ (2 : ℕ) := by
  have hmax := scoreMaximizingIndex_isMaxOn a G⁻¹
  rw [isMaxOn_univ_iff] at hmax
  have hscore := hmax j
  rw [centralSymmetryScore_inv_eq_dualNorm_sq a hG j,
    centralSymmetryScore_inv_eq_dualNorm_sq a hG (scoreMaximizingIndex a G⁻¹)] at hscore
  rw [dualNorm_sq_eq_coordinate_sq_div_det_of_dim_one hG (a j),
    dualNorm_sq_eq_coordinate_sq_div_det_of_dim_one hG (a (scoreMaximizingIndex a G⁻¹))] at hscore
  have hmul :
      (a j).ofLp 0 ^ (2 : ℕ) * Matrix.det G ≤
        (a (scoreMaximizingIndex a G⁻¹)).ofLp 0 ^ (2 : ℕ) * Matrix.det G :=
    (div_le_div_iff₀ hG.det_pos hG.det_pos).mp hscore
  nlinarith [hmul, hG.det_pos]

/-- Helper for Proposition 7.17: in dimension `1`, a vector whose coordinate square is bounded by
that of `g` has dual norm at most `1` for the rank-one matrix `ggᵀ`. -/
private lemma dualNorm_le_one_of_coordinateSq_le_dimOne
    {g x : EuclideanSpace ℝ (Fin 1)} (hg : g ≠ 0)
    (hx : x.ofLp 0 ^ (2 : ℕ) ≤ g.ofLp 0 ^ (2 : ℕ)) :
    ‖x‖[⟨Matrix.vecMulVec g g, vecMulVec_posDef_of_ne_zero_dim_one (n := 1) rfl hg⟩,*] ≤ 1 := by
  let G : Matrix (Fin 1) (Fin 1) ℝ := Matrix.vecMulVec g g
  let hG : G.PosDef := vecMulVec_posDef_of_ne_zero_dim_one (n := 1) rfl hg
  have hg0_ne : g.ofLp 0 ≠ 0 := by
    intro hg0
    apply hg
    ext i
    fin_cases i
    simpa using hg0
  have hg_sq_pos : 0 < g.ofLp 0 ^ (2 : ℕ) := by
    simpa [pow_two] using sq_pos_of_ne_zero hg0_ne
  have hsq_le :
      ‖x‖[⟨G, hG⟩,*] ^ (2 : ℕ) ≤ 1 := by
    calc
      ‖x‖[⟨G, hG⟩,*] ^ (2 : ℕ)
          = (x.ofLp 0) ^ (2 : ℕ) / Matrix.det G := by
              rw [dualNorm_sq_eq_coordinate_sq_div_det_of_dim_one hG]
      _ = (x.ofLp 0) ^ (2 : ℕ) / (g.ofLp 0 ^ (2 : ℕ)) := by
            simp [G, Matrix.det_fin_one, Matrix.vecMulVec_apply, pow_two]
      _ ≤ 1 := by
            exact (div_le_iff₀ hg_sq_pos).2 <| by simpa using hx
  have hnorm_nonneg : 0 ≤ ‖x‖[⟨G, hG⟩,*] := by
    rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
    exact Real.sqrt_nonneg _
  have hsq_one : ‖x‖[⟨G, hG⟩,*] ^ (2 : ℕ) ≤ 1 ^ (2 : ℕ) := by simpa using hsq_le
  nlinarith

/-- Helper for Proposition 7.17: in dimension `1`, the finite-family recursive method stops by
time `1`, and the displayed bound is already enough for that stopping index. -/
private theorem finiteFamilyStoppingData_ofDimOne
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn1 : n = 1) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ method : CentralSymmetricRoundingMethod n,
      (method.body : Set E) = absConvexHull ℝ (Set.range a) ∧
      method.initialMatrix = centralSymmetryGramMatrix a ∧
      method.gamma = γ ∧
      ∃ hTerminate : method.Terminates,
        ((method.stoppingIndex hTerminate : ℝ) ≤
          maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ) ∧
        centeredMatrixEllipsoid (method (method.stoppingIndex hTerminate)) 1 ⊆
          (method.body : Set E) := by
  subst hn1
  let body : ConvexBody (EuclideanSpace ℝ (Fin 1)) := absConvexHull_range_body a
  let G0 : Matrix (Fin 1) (Fin 1) ℝ := centralSymmetryGramMatrix a
  let i0 : Fin (m : ℕ) := scoreMaximizingIndex a G0⁻¹
  have hi0_mem_max :
      a i0 ∈ (body : Set (EuclideanSpace ℝ (Fin 1))) ∧
        IsMaxOn (fun g : EuclideanSpace ℝ (Fin 1) ↦ ‖g‖[⟨G0, hGram⟩,*]) (body : Set _) (a i0) := by
    -- The initial stage uses the canonical score-maximizing generator.
    simpa [body, G0, i0, absConvexHull_range_body] using
      scoreMaximizingIndex_isMaxOn_absConvexHull_dualNorm (a := a) (G := G0) hGram
  have hi0_mem_body : a i0 ∈ (body : Set (EuclideanSpace ℝ (Fin 1))) := hi0_mem_max.1
  have hbound_nonneg :
      0 ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
    -- The displayed stopping budget is nonnegative because `γ > 1` and `m ≥ 1`.
    unfold maxAbsLinearSubdifferentialRoundingStoppingIndexBound
    have hlog_nonneg : 0 ≤ Real.log (m : ℝ) := by
      exact Real.log_nonneg (by exact_mod_cast m.2)
    positivity
  by_cases hstop0 : centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ≤ γ
  · let method : CentralSymmetricRoundingMethod 1 :=
      { one_le_dim := by norm_num
        body := body
        body_balanced := absConvexHull_range_body_balanced a
        gamma := γ
        one_lt_gamma := hγ
        initialMatrix := G0
        matrix := fun _ ↦ G0
        maximizer := fun _ ↦ a i0
        matrix_posDef := fun _ ↦ hGram
        matrix_zero := rfl
        maximizer_isMaxOn := by
          intro k
          -- Every stage is the initial stage for this constant method.
          simpa [body, G0, i0, absConvexHull_range_body] using hi0_mem_max
        matrix_succ_of_gt_threshold := by
          intro k
          dsimp
          intro hk
          have hstop0' :
              centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ≤ γ * Real.sqrt (1 : ℝ) := by
            simpa using hstop0
          have hk' : γ * Real.sqrt (1 : ℝ) < centralSymmetricRoundingRadius body ⟨G0, hGram⟩ := by
            simpa using hk
          exact (False.elim <| (not_lt_of_ge hstop0') hk') }
    have hTerminate : method.Terminates := by
      refine ⟨0, ?_⟩
      -- The initial iterate already satisfies the one-dimensional stopping threshold.
      simpa [CentralSymmetricRoundingMethod.stoppingCriterion, method, body, G0] using hstop0
    have hidx0 : method.stoppingIndex hTerminate = 0 := by
      have hleast0 : method.stoppingIndex hTerminate ≤ 0 :=
        (method.stoppingIndex_isLeast hTerminate).2 <| by
          simpa [CentralSymmetricRoundingMethod.stoppingCriterion, method, body, G0] using hstop0
      exact Nat.le_zero.mp hleast0
    refine ⟨method, rfl, rfl, rfl, hTerminate, ?_, ?_⟩
    · -- The stopping index is `0`, so the explicit bound follows from its nonnegativity.
      simpa [hidx0] using hbound_nonneg
    · -- The initial Gram unit ellipsoid is already inside the canonical absolutely convex hull.
      simpa [method, body, G0, hidx0, absConvexHull_range_body] using
        initialUnitEllipsoid_subset_absConvexHull a hGram
  · have hγ_lt_radius0 : γ < centralSymmetricRoundingRadius body ⟨G0, hGram⟩ := lt_of_not_ge hstop0
    have hradius0_eq :
        centralSymmetricRoundingRadius body ⟨G0, hGram⟩ =
          ‖a i0‖[⟨G0, hGram⟩,*] := by
      have hi0_nonneg : 0 ≤ ‖a i0‖[⟨G0, hGram⟩,*] := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        exact Real.sqrt_nonneg _
      -- Rewrite the owner-side radius through the selected initial maximizer.
      calc
        centralSymmetricRoundingRadius body ⟨G0, hGram⟩
            = centralSymmetrySelectedRadius a G0⁻¹ i0 := by
                simpa [body, G0, i0] using
                  centralSymmetricRoundingRadius_eq_scoreMaximizingIndex_selectedRadius
                    (a := a) (G := G0) hGram
        _ = ‖a i0‖[⟨G0, hGram⟩,*] := by
              rw [centralSymmetrySelectedRadius, centralSymmetryScore_inv_eq_dualNorm_sq a hGram i0]
              simpa [pow_two, abs_of_nonneg hi0_nonneg] using
                (Real.sqrt_sq_eq_abs ‖a i0‖[⟨G0, hGram⟩,*])
    have hg0_ne : a i0 ≠ 0 := by
      intro hg0
      have hgamma_pos : 0 < γ := lt_trans zero_lt_one hγ
      have hnorm_pos : 0 < ‖a i0‖[⟨G0, hGram⟩,*] := by
        rw [← hradius0_eq]
        exact lt_trans hgamma_pos hγ_lt_radius0
      exact (ne_of_gt hnorm_pos) <| by
        rw [hg0]
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        simp
    have hradius0_sq_ne :
        centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ^ (2 : ℕ) - 1 ≠ 0 := by
      have hone_lt_radius0 : 1 < centralSymmetricRoundingRadius body ⟨G0, hGram⟩ :=
        lt_trans hγ hγ_lt_radius0
      nlinarith
    have hα0_one :
        centralSymmetricRoundingAlpha body ⟨G0, hGram⟩ = 1 := by
      have halpha_eq :
          centralSymmetricRoundingAlpha body ⟨G0, hGram⟩ =
            (centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ^ (2 : ℕ) - 1) /
              ((1 : ℝ) *
                (centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ^ (2 : ℕ) - 1)) := by
        simpa using centralSymmetricRoundingAlpha_eq (n := 1) body ⟨G0, hGram⟩ (by norm_num)
      -- Route correction: in the genuinely continuing one-dimensional branch, `r₀ > 1`,
      -- so the scalar denominator is nonzero and the update coefficient simplifies to `1`.
      rw [halpha_eq]
      field_simp [hradius0_sq_ne]
    let G1 : Matrix (Fin 1) (Fin 1) ℝ := Matrix.vecMulVec (a i0) (a i0)
    have hG1 : G1.PosDef := vecMulVec_posDef_of_ne_zero_dim_one (n := 1) rfl hg0_ne
    let i1 : Fin (m : ℕ) := scoreMaximizingIndex a G1⁻¹
    have hi1_mem_max :
        a i1 ∈ (body : Set (EuclideanSpace ℝ (Fin 1))) ∧
          IsMaxOn (fun g : EuclideanSpace ℝ (Fin 1) ↦ ‖g‖[⟨G1, hG1⟩,*]) (body : Set _) (a i1) := by
      -- The terminal stage again uses the canonical score-maximizing generator for its matrix.
      simpa [body, G1, i1, absConvexHull_range_body] using
        scoreMaximizingIndex_isMaxOn_absConvexHull_dualNorm (a := a) (G := G1) hG1
    have hi1_sq_le :
        (a i1).ofLp 0 ^ (2 : ℕ) ≤ (a i0).ofLp 0 ^ (2 : ℕ) := by
      -- The initial score-maximizing generator has the largest coordinate square in dimension `1`.
      simpa [G0, i0] using coordinateSq_le_scoreMaximizingIndex_of_dimOne (a := a) hGram i1
    have hi1_dual_le_one : ‖a i1‖[⟨G1, hG1⟩,*] ≤ 1 := by
      -- After the rank-one update to `ggᵀ`, every generator has dual norm at most `1`.
      simpa [G1] using dualNorm_le_one_of_coordinateSq_le_dimOne (g := a i0) hg0_ne hi1_sq_le
    have hradius1_le_one :
        centralSymmetricRoundingRadius body ⟨G1, hG1⟩ ≤ 1 := by
      have hi1_nonneg : 0 ≤ ‖a i1‖[⟨G1, hG1⟩,*] := by
        rw [positiveDefMatrixNorm_dualNorm_eq_sqrt_inner_inv]
        exact Real.sqrt_nonneg _
      calc
        centralSymmetricRoundingRadius body ⟨G1, hG1⟩
            = centralSymmetrySelectedRadius a G1⁻¹ i1 := by
                simpa [body, G1, i1] using
                  centralSymmetricRoundingRadius_eq_scoreMaximizingIndex_selectedRadius
                    (a := a) (G := G1) hG1
        _ = ‖a i1‖[⟨G1, hG1⟩,*] := by
              rw [centralSymmetrySelectedRadius, centralSymmetryScore_inv_eq_dualNorm_sq a hG1 i1]
              simpa [pow_two, abs_of_nonneg hi1_nonneg] using
                (Real.sqrt_sq_eq_abs ‖a i1‖[⟨G1, hG1⟩,*])
        _ ≤ 1 := hi1_dual_le_one
    have hstop1 :
        centralSymmetricRoundingRadius body ⟨G1, hG1⟩ ≤ γ := by
      linarith
    have hG1_eq_update :
        G1 =
          centralSymmetricRoundingUpdatedMatrix G0 (a i0)
            (centralSymmetricRoundingAlpha body ⟨G0, hGram⟩) := by
      -- At `α₀ = 1`, the update collapses to the rank-one matrix `g₀ g₀ᵀ`.
      rw [hα0_one, centralSymmetricRoundingUpdatedMatrix_eq]
      simp [G1]
    have hi0_outer :
        a i0 ∈ centeredMatrixEllipsoid G0 (Real.sqrt (m : ℝ)) := by
      have hInitial := initialGramBetaRounding_sqrt_m a hGram
      have hi0_mem_abs : a i0 ∈ absConvexHull ℝ (Set.range a) := by
        simpa [body, absConvexHull_range_body] using hi0_mem_body
      have hi0_outer' :
          a i0 ∈ matrixEllipsoid G0 (0 : EuclideanSpace ℝ (Fin 1)) (Real.sqrt (m : ℝ)) :=
        hInitial.subset_beta_ellipsoid hi0_mem_abs
      simpa [centeredMatrixEllipsoid] using hi0_outer'
    have hi0_dual_le_sqrt_card : ‖a i0‖[⟨G0, hGram⟩,*] ≤ Real.sqrt (m : ℝ) := by
      rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le hGram] at hi0_outer
    have hγ_lt_sqrt_card : γ < Real.sqrt (m : ℝ) := by
      have hradius0_le_sqrt_card :
          centralSymmetricRoundingRadius body ⟨G0, hGram⟩ ≤ Real.sqrt (m : ℝ) := by
        simpa [hradius0_eq] using hi0_dual_le_sqrt_card
      exact lt_of_lt_of_le hγ_lt_radius0 hradius0_le_sqrt_card
    have hinner1 :
        centeredMatrixEllipsoid G1 1 ⊆ (body : Set (EuclideanSpace ℝ (Fin 1))) := by
      let weights1 : StdSimplex ℝ (Fin (m : ℕ)) := StdSimplex.single i0
      have hrep1 : G1 = B[a](weights1.weights) := by
        ext p q
        rw [weightedGramMatrix_apply]
        rw [Finset.sum_eq_single i0]
        · simp [weights1, G1, Matrix.vecMulVec_apply]
        · intro x _ hx
          simp [weights1, hx]
        · intro hi0
          exact False.elim (hi0 <| by simp)
      -- Re-express the rank-one terminal matrix as a singleton weighted-Gram stage.
      simpa [body, absConvexHull_range_body] using
        weightedGramUnitEllipsoidSubsetAbsConvexHull (a := a) weights1 hG1 hrep1
    let method : CentralSymmetricRoundingMethod 1 :=
      { one_le_dim := by norm_num
        body := body
        body_balanced := absConvexHull_range_body_balanced a
        gamma := γ
        one_lt_gamma := hγ
        initialMatrix := G0
        matrix := fun
          | 0 => G0
          | _ + 1 => G1
        maximizer := fun
          | 0 => a i0
          | _ + 1 => a i1
        matrix_posDef := by
          intro k
          cases k with
          | zero =>
              simpa [G0]
          | succ k =>
              simpa [G1] using hG1
        matrix_zero := rfl
        maximizer_isMaxOn := by
          intro k
          cases k with
          | zero =>
              -- Stage `0` uses the initial score maximizer.
              simpa [body, G0, i0, absConvexHull_range_body] using hi0_mem_max
          | succ k =>
              -- Every later stage is the constant rank-one terminal matrix.
              simpa [body, G1, i1, absConvexHull_range_body] using hi1_mem_max
        matrix_succ_of_gt_threshold := by
          intro k
          dsimp
          intro hk
          cases k with
          | zero =>
              -- The only genuine update is the first step from `G₀` to the rank-one matrix `G₁`.
              simpa [body, G0, G1, i0] using hG1_eq_update
          | succ k =>
              have hstop1' :
                  centralSymmetricRoundingRadius body ⟨G1, hG1⟩ ≤ γ * Real.sqrt (1 : ℝ) := by
                simpa using hstop1
              have hk_false :
                  ¬ γ * Real.sqrt (1 : ℝ) < centralSymmetricRoundingRadius body ⟨G1, hG1⟩ :=
                not_lt_of_ge hstop1'
              exact (False.elim <| hk_false <| by simpa [body, G1] using hk) }
    have hTerminate : method.Terminates := by
      refine ⟨1, ?_⟩
      -- The rank-one stage already satisfies the one-dimensional stopping threshold.
      simpa [CentralSymmetricRoundingMethod.stoppingCriterion, method, body, G1] using hstop1
    have hnot_method_stop0 : ¬ method.stoppingCriterion 0 := by
      simpa [CentralSymmetricRoundingMethod.stoppingCriterion, method, body, G0] using hstop0
    have hidx_le_one : method.stoppingIndex hTerminate ≤ 1 :=
      (method.stoppingIndex_isLeast hTerminate).2 <| by
        simpa [CentralSymmetricRoundingMethod.stoppingCriterion, method, body, G1] using hstop1
    have hidx_eq_one : method.stoppingIndex hTerminate = 1 := by
      have hidx_ne_zero : method.stoppingIndex hTerminate ≠ 0 := by
        intro hidx0
        exact hnot_method_stop0 <| by simpa [hidx0] using method.stoppingIndex_spec hTerminate
      omega
    refine ⟨method, rfl, rfl, rfl, hTerminate, ?_, ?_⟩
    · -- The first stopping index is `1`, and the displayed budget already dominates `1`.
      calc
        (method.stoppingIndex hTerminate : ℝ) = 1 := by exact_mod_cast hidx_eq_one
        _ ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ :=
          one_le_stoppingBound_of_lt_sqrt_card hγ hγ_lt_sqrt_card
    · -- The canonical stopping iterate is the rank-one stage with its singleton weighted-Gram
      -- inner containment.
      simpa [hidx_eq_one, method, body, G1] using hinner1

-- Semantic recall note: `lean_leansearch` did not expose any closer existing owner for this
-- Chapter 7 computability claim, so the repaired statement uses the lighter
-- `CentralSymmetricRoundingMethod` owner instead of the inconsistent stronger
-- `CentralSymmetryRoundingAlgorithm` record.
/-- Certificate data for the centrally symmetric rounding run attached to a finite family
`a₁, …, aₘ` and threshold `γ`. -/
structure MaxAbsLinearSubdifferentialRoundingCertificate
    {m : ℕ+} (a : Fin (m : ℕ) → E) (γ : ℝ) where
  method : CentralSymmetricRoundingMethod n
  body_eq : (method.body : Set E) = absConvexHull ℝ (Set.range a)
  initialMatrix_eq : method.initialMatrix = centralSymmetryGramMatrix a
  gamma_eq : method.gamma = γ
  hTerminate : method.Terminates
  isEllipsoidal :
    let s := method.stoppingIndex hTerminate
    IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ (method s)

namespace MaxAbsLinearSubdifferentialRoundingCertificate

/-- The canonical first accepted iterate of the certified centrally symmetric rounding run. -/
def stoppingIndex
    {m : ℕ+} {a : Fin (m : ℕ) → E} {γ : ℝ}
    (certificate : MaxAbsLinearSubdifferentialRoundingCertificate a γ) : ℕ :=
  certificate.method.stoppingIndex certificate.hTerminate

/-- The certified run is a `γ √n`-ellipsoidal rounding at its stopping index. -/
theorem isEllipsoidal_at_stoppingIndex
    {m : ℕ+} {a : Fin (m : ℕ) → E} {γ : ℝ}
    (certificate : MaxAbsLinearSubdifferentialRoundingCertificate a γ) :
    IsEllipsoidalRounding
      (absConvexHull ℝ (Set.range a)) γ
      (certificate.method certificate.stoppingIndex) := by
  simpa [stoppingIndex] using certificate.isEllipsoidal

end MaxAbsLinearSubdifferentialRoundingCertificate

/-- Helper for Proposition 7.17: at every stage of a centrally symmetric rounding method, the
chosen maximizer realizes the current radius. -/
private lemma centralSymmetricRoundingMethod_radius_eq_maximizerDualNorm
    (method : CentralSymmetricRoundingMethod n) (k : ℕ) :
    method.radius k =
      ‖method.maximizer k‖[⟨method k, method.matrix_posDef k⟩,*] := by
  let G : {G : Matrix (Fin n) (Fin n) ℝ // G.PosDef} := ⟨method k, method.matrix_posDef k⟩
  rcases method.maximizer_isMaxOn k with ⟨hk_mem, hk_max⟩
  have hk_lub :
      IsLUB
        ((fun g : E ↦ ‖g‖[G,*]) '' ((method.body : ConvexBody E) : Set E))
        ‖method.maximizer k‖[G,*] := by
    -- The selected maximizer is an actual maximum of the dual norm on the body.
    simpa [G, isMaxOn_iff] using hk_max.isLUB hk_mem
  -- Replace the radius supremum by the value attained at the maximizing point.
  rw [CentralSymmetricRoundingMethod.radius_eq, centralSymmetricRoundingRadius_eq_sSup]
  exact hk_lub.csSup_eq
    ⟨‖method.maximizer k‖[G,*], ⟨method.maximizer k, hk_mem, rfl⟩⟩

/-- Helper for Proposition 7.17: once a centrally symmetric rounding method reaches a stopping
iterate whose unit ellipsoid is still inside the body, that iterate is already a
`γ √n`-ellipsoidal rounding of the canonical absolutely convex hull. -/
private lemma isEllipsoidal_of_stoppingCriterion
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E)
    (method : CentralSymmetricRoundingMethod n)
    (hbody : (method.body : Set E) = absConvexHull ℝ (Set.range a))
    (hgamma_eq : method.gamma = γ) {k : ℕ}
    (hinner : centeredMatrixEllipsoid (method k) 1 ⊆ (method.body : Set E))
    (hstop : method.stoppingCriterion k) :
    IsEllipsoidalRounding (absConvexHull ℝ (Set.range a)) γ (method k) := by
  refine ⟨method.matrix_posDef k, ?_⟩
  refine ⟨?_, ?_⟩
  · -- Rewrite the stagewise inner containment into the centered ellipsoid owner.
    simpa [hbody, centeredMatrixEllipsoid_one_eq_affineEllipsoid] using hinner
  · intro x hx
    have hx_body : x ∈ (method.body : Set E) := by
      simpa [hbody] using hx
    rcases method.maximizer_isMaxOn k with ⟨_, hk_max⟩
    have hx_le_max :
        ‖x‖[⟨method k, method.matrix_posDef k⟩,*] ≤
          ‖method.maximizer k‖[⟨method k, method.matrix_posDef k⟩,*] :=
      hk_max hx_body
    have hx_le_stop :
        ‖x‖[⟨method k, method.matrix_posDef k⟩,*] ≤ γ * Real.sqrt (n : ℝ) := by
      -- The stopping threshold controls every body point through the maximizing dual norm.
      calc
        ‖x‖[⟨method k, method.matrix_posDef k⟩,*] ≤
            ‖method.maximizer k‖[⟨method k, method.matrix_posDef k⟩,*] := hx_le_max
        _ = method.radius k := by
              symm
              exact centralSymmetricRoundingMethod_radius_eq_maximizerDualNorm method k
        _ ≤ method.gamma * Real.sqrt (n : ℝ) := hstop
        _ = γ * Real.sqrt (n : ℝ) := by rw [hgamma_eq]
    have hx_outer : x ∈ centeredMatrixEllipsoid (method k) (γ * Real.sqrt (n : ℝ)) := by
      rwa [mem_centeredMatrixEllipsoid_iff_dualNorm_le (method.matrix_posDef k)]
    simpa [centeredMatrixEllipsoid] using hx_outer

/-- Proposition 7.17: under the standard side conditions used by the Chapter 7 method, one
obtains a certified centrally symmetric rounding run for `∂f(0) = conv {± aᵢ}`. -/
theorem exists_centralSymmetryRoundingAlgorithm_of_maxAbsLinearSubdifferential_stoppingIndex_le
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hn : 1 ≤ n) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ certificate : MaxAbsLinearSubdifferentialRoundingCertificate a γ, True := by
  have hmethod :
      ∃ method : CentralSymmetricRoundingMethod n,
        (method.body : Set E) = absConvexHull ℝ (Set.range a) ∧
        method.initialMatrix = centralSymmetryGramMatrix a ∧
        method.gamma = γ ∧
        ∃ hTerminate : method.Terminates,
          centeredMatrixEllipsoid (method (method.stoppingIndex hTerminate)) 1 ⊆
            (method.body : Set E) := by
    by_cases hdim_one : n = 1
    · -- Route correction: in dimension `1`, the recursive finite-family method already stops by
      -- time `1`, so the branch closes directly from the `sqrt m` initial rounding.
      rcases finiteFamilyStoppingData_ofDimOne a hdim_one hγ hGram with
        ⟨method, hbody, hinit, hgamma_eq, hTerminate, _hbound, hinner⟩
      exact ⟨method, hbody, hinit, hgamma_eq, hTerminate, hinner⟩
    · have hn2 : 2 ≤ n := by
        omega
      rcases finiteFamilyMethodData_ofTwoLe a hn2 hγ hGram with
        ⟨method, weights, hbody, hinit, hgamma_eq, hstage, hweights0, hweights_pos,
          hweights_succ, hinner_all⟩
      have hstopExists : method.Terminates := by
        let T : ℕ :=
          Nat.floor ((n : ℝ) * maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ) + 1
        by_contra hno
        have hnostop : ∀ k : ℕ, k < T → ¬ method.stoppingCriterion k := by
          intro k hk
          exact fun hkStop ↦ hno ⟨k, hkStop⟩
        let c : ℝ := (γ - 1) ^ (2 : ℕ) / γ ^ (2 : ℕ)
        have hc_pos : 0 < c := by
          dsimp [c]
          have hgamma_sub_pos : 0 < γ - 1 := sub_pos.mpr hγ
          positivity
        have hstep :
            ∀ k : ℕ, k < T →
              c ≤ Real.log (Matrix.det (method (k + 1))) - Real.log (Matrix.det (method k)) := by
          intro k hk
          simpa [c] using
            logDetIncrement_ge_uniformDrop_of_not_stopping method hn2 hgamma_eq hγ (hnostop k hk)
        have hlower :=
          CentralSymmetricRoundingMethod.logdet_growth_lower_bound_upto
            (method := method) (T := T) (c := c) hstep
        have hzero :
            method 0 = centralSymmetryGramMatrix a := by
          calc
            method 0 = method.initialMatrix := method.matrix_zero
            _ = centralSymmetryGramMatrix a := hinit
        have hInitial :
            IsBetaRounding (method.body : Set E) (Real.sqrt (m : ℝ)) (method 0) (0 : E) := by
          simpa [hbody, hzero] using initialGramBetaRounding_sqrt_m a hGram
        have hupper :
            (Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0))) / (n : ℝ) ≤
              Real.log (m : ℝ) :=
          avgLogDetGain_le_log_card_of_initialRounding method hn2 hInitial (hinner_all T)
        have hn_pos_nat : 0 < n := by omega
        have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
        have hupper' :
            Real.log (Matrix.det (method T)) - Real.log (Matrix.det (method 0)) ≤
              (n : ℝ) * Real.log (m : ℝ) := by
          simpa [mul_comm] using (div_le_iff₀ hn_pos).mp hupper
        have hbudget : (T : ℝ) * c ≤ (n : ℝ) * Real.log (m : ℝ) := by
          linarith
        have hT_le_div :
            (T : ℝ) ≤ ((n : ℝ) * Real.log (m : ℝ)) / c := by
          exact (le_div_iff₀ hc_pos).2 <| by
            simpa [mul_assoc, mul_left_comm, mul_comm] using hbudget
        have hcoeff :
            ((n : ℝ) * Real.log (m : ℝ)) / c =
              (n : ℝ) * maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
          dsimp [c]
          unfold maxAbsLinearSubdifferentialRoundingStoppingIndexBound
          have hgamma_ne : γ ≠ 0 := by linarith
          have hgamma_sub_ne : γ - 1 ≠ 0 := by linarith
          field_simp [hgamma_ne, hgamma_sub_ne]
        have hT_le :
            (T : ℝ) ≤ (n : ℝ) * maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
          rw [hcoeff] at hT_le_div
          exact hT_le_div
        have hT_lt :
            (n : ℝ) * maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ < T := by
          simpa [T] using
            (Nat.lt_floor_add_one
              ((n : ℝ) * maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ))
        exact (not_lt_of_ge hT_le) hT_lt
      exact ⟨method, hbody, hinit, hgamma_eq, hstopExists,
        hinner_all (method.stoppingIndex hstopExists)⟩
  rcases hmethod with
    ⟨method, hbody, hinit, hgamma_eq, hTerminate, hinner⟩
  refine ⟨
    { method := method
      body_eq := hbody
      initialMatrix_eq := hinit
      gamma_eq := hgamma_eq
      hTerminate := hTerminate
      isEllipsoidal := ?_ },
    trivial⟩
  -- The stopping iterate already satisfies the centered ellipsoidal-rounding conditions.
  exact isEllipsoidal_of_stoppingCriterion a method hbody hgamma_eq hinner
    (method.stoppingIndex_spec hTerminate)

-- Proof sketch: combine the preprocessing bound `n² (n + 6m) / 6` for the quantities defining
-- the subdifferential `∂f(0) = conv {± aᵢ}` with the central-symmetry rounding complexity bound
-- `(γ² / (γ - 1)²) n² (2m + 3n) log m`; the source-facing conclusion is phrased directly as the
-- existence of a rounding matrix together with a witness step count satisfying the displayed
-- arithmetic-work inequality, while the positive-definiteness of the initial Gram matrix remains
-- as the explicit Chapter 7 admissibility assumption on the input family.
/-- Existence conclusion of Proposition 7.17: if the Chapter 7 input family `a₁, …, aₘ`
defining `∂f(0) = conv {± aᵢ}` has positive-definite initial Gram matrix, then there exist a
`γ √n`-rounding `G` of `absConvexHull ℝ (Set.range a)` with relative accuracy `γ` and a step count
witnessing that it can be computed using at most
`n² (n + 6m) / 6 + (γ² / (γ - 1)²) n² (2m + 3n) log m`
arithmetic operations. -/
theorem exists_centralSymmetryRoundingAlgorithm_of_maxAbsLinearSubdifferential
    {m : ℕ+} {γ : ℝ} (a : Fin (m : ℕ) → E) (hγ : 1 < γ)
    (hGram : (centralSymmetryGramMatrix a).PosDef) :
    ∃ steps : ℕ, ∃ G : Matrix (Fin n) (Fin n) ℝ,
      IsEllipsoidalRounding
          (absConvexHull ℝ (Set.range a)) γ G ∧
        ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
            (steps : ℝ) * (n : ℝ) ^ (2 : ℕ) * (2 * (m : ℝ) + 3 * (n : ℝ)) ≤
          maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ := by
  by_cases hn : 1 ≤ n
  · -- In positive dimension, extract the certified stopping iterate from the preceding theorem.
    obtain ⟨certificate, _⟩ :=
      exists_centralSymmetryRoundingAlgorithm_of_maxAbsLinearSubdifferential_stoppingIndex_le
        a hn hγ hGram
    refine ⟨0, certificate.method certificate.stoppingIndex, ?_, ?_⟩
    · -- The certificate already packages the required `γ √n`-ellipsoidal rounding.
      exact certificate.isEllipsoidal_at_stoppingIndex
    · -- Compare the linear-in-steps work term with the displayed stopping-index upper bound.
      have hstop_nonneg :
          0 ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ := by
        exact maxAbsLinearSubdifferentialRoundingStoppingIndexBound_nonneg hγ
      have hfactor_nonneg :
          0 ≤ maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ *
            (n : ℝ) ^ (2 : ℕ) * (2 * (m : ℝ) + 3 * (n : ℝ)) := by
        positivity
      calc
        ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
            (((0 : ℕ) : ℝ) * (n : ℝ) ^ (2 : ℕ) * (2 * (m : ℝ) + 3 * (n : ℝ)))
            = ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) := by ring
        _ ≤ ((n : ℝ) ^ (2 : ℕ) / 6) * ((n : ℝ) + 6 * (m : ℝ)) +
              maxAbsLinearSubdifferentialRoundingStoppingIndexBound m γ *
                (n : ℝ) ^ (2 : ℕ) * (2 * (m : ℝ) + 3 * (n : ℝ)) := by
              exact le_add_of_nonneg_right hfactor_nonneg
        _ = maxAbsLinearSubdifferentialRoundingArithmeticWorkBound m n γ := by
              rw [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound]
  · have hn0 : n = 0 := by
      omega
    subst hn0
    refine ⟨0, centralSymmetryGramMatrix a, ?_, ?_⟩
    · -- In dimension `0`, every point is `0`, so the unique matrix already rounds the singleton
      -- body `absConvexHull ℝ (Set.range a)`.
      refine ⟨hGram, ?_⟩
      refine ⟨?_, ?_⟩
      · intro x hx
        have hzero : (0 : EuclideanSpace ℝ (Fin 0)) ∈ absConvexHull ℝ (Set.range a) :=
          zero_mem_absConvexHull
        have hx0 : x = 0 := Subsingleton.elim _ _
        simpa [hx0] using hzero
      · intro x hx
        have hx0 : x = 0 := Subsingleton.elim _ _
        rw [hx0]
        simpa [mem_centeredMatrixEllipsoid_iff]
    · -- The rounding-cost term vanishes because `n = 0`.
      simp [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound]

-- Proof sketch: for fixed `γ > 1`, the factor `γ² / (γ - 1)²` is a constant depending only on
-- `γ`. The polynomial factors satisfy
-- `n² (n + 6m) = O(n² (n + m))` and `n² (2m + 3n) = O(n² (n + m))`, so the explicit bound is
-- controlled by `n² (n + m) log m` on the admissible domain `m ≥ 2`; this is stated directly on
-- mathlib's canonical `=O[l]` surface with `l = principal { (m, n) | 2 ≤ m }`.
/-- In particular for Proposition 7.17, the explicit arithmetic bound has growth
`O(n² (n + m) log m)` on the domain `m ≥ 2`, expressed on the canonical
`Asymptotics.IsBigO` surface. -/
theorem maxAbsLinearSubdifferentialRoundingArithmeticWorkBound_isBigO_n_sq_mul_n_add_m_log
    {γ : ℝ} (hγ : 1 < γ) :
    (fun dims : ℕ+ × ℕ ↦
      maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ) =O[
        principal (setOf fun dims : ℕ+ × ℕ ↦ 2 ≤ (dims.1 : ℕ))]
      (fun dims ↦
        (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)) := by
  let κ : ℝ := γ ^ (2 : ℕ) / (γ - 1) ^ (2 : ℕ)
  let C : ℝ := 1 / Real.log (2 : ℝ) + 3 * κ
  refine IsBigO.of_bound C ?_
  rw [Filter.eventually_principal]
  intro dims hdims
  have hm_two_le : (2 : ℝ) ≤ (dims.1 : ℝ) := by
    exact_mod_cast hdims
  have hm_pos : 0 < (dims.1 : ℝ) := by
    positivity
  have hlog_two_pos : 0 < Real.log (2 : ℝ) := by
    exact Real.log_pos one_lt_two
  have hlogm_nonneg : 0 ≤ Real.log (dims.1 : ℝ) := by
    exact Real.log_nonneg (le_trans (by norm_num) hm_two_le)
  have hlog_two_le : Real.log (2 : ℝ) ≤ Real.log (dims.1 : ℝ) := by
    exact Real.log_le_log (by norm_num) hm_two_le
  have hk_nonneg : 0 ≤ κ := by
    have hgamma_sub_pos : 0 < γ - 1 := sub_pos.mpr hγ
    positivity
  let g : ℝ :=
    (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) * Real.log (dims.1 : ℝ)
  have hg_nonneg : 0 ≤ g := by
    dsimp [g]
    positivity
  -- The preprocessing term is absorbed using `log m ≥ log 2 > 0` on the admissible domain.
  have hpre :
      ((dims.2 : ℝ) ^ (2 : ℕ) / 6) * ((dims.2 : ℝ) + 6 * (dims.1 : ℝ)) ≤
        (1 / Real.log (2 : ℝ)) * g := by
    have hlin :
        (dims.2 : ℝ) + 6 * (dims.1 : ℝ) ≤
          6 * ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
      nlinarith
    have hstep1 :
        ((dims.2 : ℝ) ^ (2 : ℕ) / 6) * ((dims.2 : ℝ) + 6 * (dims.1 : ℝ)) ≤
          ((dims.2 : ℝ) ^ (2 : ℕ) / 6) * (6 * ((dims.2 : ℝ) + (dims.1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hlin (by positivity)
    have hstep2 :
        ((dims.2 : ℝ) ^ (2 : ℕ) / 6) * (6 * ((dims.2 : ℝ) + (dims.1 : ℝ))) =
          (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
      ring
    have hcore :
        (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) ≤
          (1 / Real.log (2 : ℝ)) * g := by
      have hAlog :
          ((dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) * Real.log (2 : ℝ) ≤
            ((dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) *
              Real.log (dims.1 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hlog_two_le (by positivity)
      have hlog_two_inv_nonneg : 0 ≤ 1 / Real.log (2 : ℝ) := by
        positivity
      calc
        (dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ))
            = (1 / Real.log (2 : ℝ)) *
                (((dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) *
                  Real.log (2 : ℝ)) := by
              field_simp [hlog_two_pos.ne']
        _ ≤ (1 / Real.log (2 : ℝ)) *
              (((dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ))) *
                Real.log (dims.1 : ℝ)) := by
              exact mul_le_mul_of_nonneg_left hAlog hlog_two_inv_nonneg
        _ = (1 / Real.log (2 : ℝ)) * g := by
              dsimp [g]
    exact le_trans (by simpa [hstep2] using hstep1) hcore
  -- The rounding term is absorbed by the linear inequality `2m + 3n ≤ 3 (n + m)`.
  have hround :
      κ * (dims.2 : ℝ) ^ (2 : ℕ) * (2 * (dims.1 : ℝ) + 3 * (dims.2 : ℝ)) *
          Real.log (dims.1 : ℝ) ≤
        (3 * κ) * g := by
    have hlin :
        2 * (dims.1 : ℝ) + 3 * (dims.2 : ℝ) ≤
          3 * ((dims.2 : ℝ) + (dims.1 : ℝ)) := by
      nlinarith
    have hfactor_nonneg :
        0 ≤ κ * (dims.2 : ℝ) ^ (2 : ℕ) * Real.log (dims.1 : ℝ) := by
      positivity
    have hmul :
        (κ * (dims.2 : ℝ) ^ (2 : ℕ) * Real.log (dims.1 : ℝ)) *
            (2 * (dims.1 : ℝ) + 3 * (dims.2 : ℝ)) ≤
          (κ * (dims.2 : ℝ) ^ (2 : ℕ) * Real.log (dims.1 : ℝ)) *
            (3 * ((dims.2 : ℝ) + (dims.1 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hlin hfactor_nonneg
    simpa [g, κ, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hbound :
      maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ ≤ C * g := by
    have hsum := add_le_add hpre hround
    have hcombine :
        (1 / Real.log (2 : ℝ)) * g + (3 * κ) * g ≤ C * g := by
      dsimp [C]
      ring_nf
      nlinarith [hg_nonneg]
    exact le_trans (by simpa [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound, κ,
      maxAbsLinearSubdifferentialRoundingStoppingIndexBound, g, mul_assoc, mul_left_comm,
      mul_comm] using hsum) hcombine
  have hwork_nonneg :
      0 ≤ maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ := by
    rw [maxAbsLinearSubdifferentialRoundingArithmeticWorkBound_eq]
    positivity
  calc
    ‖maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ‖ =
        maxAbsLinearSubdifferentialRoundingArithmeticWorkBound dims.1 dims.2 γ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hwork_nonneg]
    _ ≤ C * g := hbound
    _ = C *
          ‖(dims.2 : ℝ) ^ (2 : ℕ) * ((dims.2 : ℝ) + (dims.1 : ℝ)) *
              Real.log (dims.1 : ℝ)‖ := by
          rw [Real.norm_eq_abs, abs_of_nonneg hg_nonneg]

end
