/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricFiberLengthOneExtraction

public section

open scoped BigOperators ContDiff NNReal

namespace LocalInvariantGraph

/-- Helper for cm-center-proposition: a multilinear branch of the composition
formula is bounded by its operator norm times one common bound for every slot. -/
theorem norm_partitionEvaluation_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {r : ℕ} (c : OrderedFinpartition r)
    (jet : ∀ k : ℕ, E [×k]→L[ℝ] F) (v : ℕ → E) (A B : ℝ≥0)
    (hjet : ‖jet c.length‖ ≤ A)
    (hv : ∀ j : Fin c.length, ‖v (c.partSize j)‖ ≤ B) :
    ‖jet c.length (fun j ↦ v (c.partSize j))‖ ≤ (A : ℝ) * (B : ℝ) ^ c.length := by
  have hproduct : (∏ j : Fin c.length, ‖v (c.partSize j)‖) ≤
      ∏ _j : Fin c.length, (B : ℝ) := by
    apply Finset.prod_le_prod
    · intro j _
      exact norm_nonneg _
    · intro j _
      exact hv j
  calc
    _ ≤ ‖jet c.length‖ * ∏ j : Fin c.length, ‖v (c.partSize j)‖ :=
      (jet c.length).le_opNorm _
    _ ≤ (A : ℝ) * ∏ _j : Fin c.length, (B : ℝ) :=
      mul_le_mul hjet hproduct (Finset.prod_nonneg (fun j _ ↦ norm_nonneg _)) A.coe_nonneg
    _ = _ := by simp

/-- Helper for cm-center-proposition: after removing the single-block branch,
all inner jet slots in the finite composition sum have order strictly below `r`.
Uniform bounds on these slots and the fixed outer jets give one explicit sum bound. -/
theorem norm_nonSingleBlockSum_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ) (jet : ∀ k : ℕ, E [×k]→L[ℝ] F) (v : ℕ → E) (A B : ℝ≥0)
    (hjet : ∀ k, k ≤ r → ‖jet k‖ ≤ A)
    (hv : ∀ k, 0 < k → k < r → ‖v k‖ ≤ B) :
    ‖∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        jet c.length (fun j ↦ v (c.partSize j))‖ ≤
      ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        (A : ℝ) * (B : ℝ) ^ c.length := by
  classical
  calc
    _ ≤ ∑ c ∈ (Finset.univ.filter (fun c : OrderedFinpartition r ↦ c.length ≠ 1)),
        ‖jet c.length (fun j ↦ v (c.partSize j))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c hc
      have hlen := (Finset.mem_filter.mp hc).2
      apply norm_partitionEvaluation_le c jet v A B (hjet c.length c.length_le)
      intro j
      exact hv (c.partSize j) (c.partSize_pos j)
        (orderedFinpartition_partSize_lt_of_length_ne_one c hlen j)

/-- Helper for cm-center-proposition: deleting both extreme branches of a
composition sum leaves only outer and inner jets of orders strictly below `r`.
Their common bounds control the mixed Faà-di-Bruno remainder independently of the graph. -/
theorem norm_mixedPartitionSum_le
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℕ) (jet : ∀ k : ℕ, E [×k]→L[ℝ] F) (v : ℕ → E) (A B : ℝ≥0)
    (hjet : ∀ k, k < r → ‖jet k‖ ≤ A)
    (hv : ∀ k, 0 < k → k < r → ‖v k‖ ≤ B) :
    ‖∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        jet c.length (fun j ↦ v (c.partSize j))‖ ≤
      ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        (A : ℝ) * (B : ℝ) ^ c.length := by
  classical
  calc
    _ ≤ ∑ c ∈ (Finset.univ.filter
        (fun c : OrderedFinpartition r ↦ c.length ≠ r ∧ c.length ≠ 1)),
        ‖jet c.length (fun j ↦ v (c.partSize j))‖ := norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro c hc
      have hlen := (Finset.mem_filter.mp hc).2
      apply norm_partitionEvaluation_le c jet v A B
        (hjet c.length (lt_of_le_of_ne c.length_le hlen.1))
      intro j
      exact hv (c.partSize j) (c.partSize_pos j)
        (orderedFinpartition_partSize_lt_of_length_ne_one c hlen.2 j)

end LocalInvariantGraph
