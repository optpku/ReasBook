/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

/- Domain-style sampling for Corollary 25.32:
* primary domain: dyadic pathwise Itô integration with quadratic covariation;
* sampled owner declarations in the same domain:
  `HasQuadraticCovariationAlong`,
  `exists_quadratic_covariation_along_of_hasContinuousSquareVariation`,
  `HasPathwiseItoIntegralAlong.eq_pathwiseItoIntegralAlong`, and
  `pathwiseItoIntegralAlong`;
* owner abstraction: the canonical dyadic integral `pathwiseItoIntegralAlong` together with the
  dyadic covariation owner `HasQuadraticCovariationAlong`;
* primitive data: a chosen continuous covariation path `covXY : PathSpace`;
* derived API: the product-rule identity and the polarization corollary below.

Layer triage:
* source-facing: the product-rule identity for `X Y`;
* core/canonical: `HasQuadraticCovariationAlong` and `pathwiseItoIntegralAlong`;
* bridge/view: Corollary 25.32, which rewrites the source formula through those owners. -/

/-- Helper for Corollary 25.32: every partition point strictly before the truncation index lies
strictly below the terminal time. -/
private lemma partitionPoint_lt_time_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  -- Proof comment: if `P n k` had already reached `T`, minimality of the truncation index would
  -- force `partitionBoundIndex P n T ≤ k`, contradicting `hk`.
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin : partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Corollary 25.32: each finite dyadic row satisfies the discrete product
decomposition used to compare the `Y dX` and `X dY` sums. -/
private lemma dyadicProductRowDecomposition
    (X Y : PathSpace) (T : NNReal) (n : ℕ) :
    partitionPathwiseItoApproximationUpTo Y X dyadicPartitionSequence T n =
      X T * Y T - X 0 * Y 0 -
        partitionPathwiseItoApproximationUpTo X Y dyadicPartitionSequence T n -
        partitionQuadraticCovariationSum dyadicPartitionSequence X Y T n := by
  let point : ℕ → NNReal := fun k ↦ min (dyadicPartitionSequence n k) T
  let m := partitionBoundIndex dyadicPartitionSequence n T
  have hpoint_zero : point 0 = 0 := by
    -- Proof comment: truncating the dyadic row at `T` still leaves the initial point at `0`.
    simp [point, Definition2158.dyadicPartitionSequence]
  have hpoint_bound : point m = T := by
    -- Proof comment: the cutoff index is chosen so that the corresponding dyadic point has
    -- already reached `T`.
    dsimp [point, m]
    rw [min_eq_right]
    simpa using le_partitionBoundIndex_time dyadicPartitionSequence n T
  have hpoint_left : ∀ k, k < m → point k = dyadicPartitionSequence n k := by
    intro k hk
    -- Proof comment: before the cutoff index each left endpoint still lies below `T`, so the
    -- truncation by `min T` does not change it.
    dsimp [point, m]
    rw [min_eq_left]
    exact le_of_lt
      (partitionPoint_lt_time_of_lt_partitionBoundIndex dyadicPartitionSequence n k T hk)
  have htelescoping :
      X (point m) * Y (point m) =
        X (point 0) * Y (point 0) +
          Finset.sum (Finset.range m) fun k ↦
            (X (point (k + 1)) * Y (point (k + 1)) - X (point k) * Y (point k)) := by
    -- Proof comment: telescope the product increments along the truncated dyadic row.
    simpa using (Finset.eq_sum_range_sub (fun k ↦ X (point k) * Y (point k)) m)
  have hprod :
      X T * Y T - X 0 * Y 0 =
        partitionPathwiseItoApproximationUpTo Y X dyadicPartitionSequence T n +
          partitionPathwiseItoApproximationUpTo X Y dyadicPartitionSequence T n +
          partitionQuadraticCovariationSum dyadicPartitionSequence X Y T n := by
    calc
      X T * Y T - X 0 * Y 0
          = X (point m) * Y (point m) - X (point 0) * Y (point 0) := by
              rw [hpoint_bound, hpoint_zero]
      _ =
          Finset.sum (Finset.range m) fun k ↦
            (X (point (k + 1)) * Y (point (k + 1)) - X (point k) * Y (point k)) := by
              linarith [htelescoping]
      _ =
          Finset.sum (Finset.range m) fun k ↦
            (Y (dyadicPartitionSequence n k) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                  X (dyadicPartitionSequence n k)) +
              X (dyadicPartitionSequence n k) *
                (Y (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                  Y (dyadicPartitionSequence n k)) +
              (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                  X (dyadicPartitionSequence n k)) *
                (Y (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                  Y (dyadicPartitionSequence n k))) := by
              -- Proof comment: rewrite each telescoping product increment in the standard
              -- `ΔX`, `ΔY` form at the current dyadic row.
              refine Finset.sum_congr rfl fun k hk ↦ ?_
              have hk' : k < m := Finset.mem_range.mp hk
              rw [hpoint_left k hk']
              change
                X (partitionNextPointUpTo dyadicPartitionSequence n k T) *
                    Y (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                  X (dyadicPartitionSequence n k) * Y (dyadicPartitionSequence n k) =
                _
              ring
      _ =
          partitionPathwiseItoApproximationUpTo Y X dyadicPartitionSequence T n +
            partitionPathwiseItoApproximationUpTo X Y dyadicPartitionSequence T n +
            partitionQuadraticCovariationSum dyadicPartitionSequence X Y T n := by
              -- Proof comment: regroup the three finite sums back into the owner declarations.
              simp [partitionPathwiseItoApproximationUpTo, partitionQuadraticCovariationSum, m,
                Finset.sum_add_distrib, add_assoc]
  linarith

/-- Helper for Corollary 25.32: the known `X dY` realization together with the chosen quadratic
covariation gives the complementary `Y dX` realization. -/
private lemma hasPathwiseItoIntegralAlong_swap_of_quadraticCovariation
    {X Y : PathSpace}
    (hItoXY :
      HasPathwiseItoIntegralAlong
        X
        Y
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong X Y dyadicPartitionSequence))
    (covXY : PathSpace)
    (hcovXY : HasQuadraticCovariationAlong X Y covXY) :
    HasPathwiseItoIntegralAlong
      Y
      X
      dyadicPartitionSequence
      (fun T ↦
        X T * Y T - X 0 * Y 0 -
          (pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T)) := by
  intro T
  have hsum :
      Tendsto
        (fun n ↦
          partitionPathwiseItoApproximationUpTo X Y dyadicPartitionSequence T n +
            partitionQuadraticCovariationSum dyadicPartitionSequence X Y T n)
        atTop
        (nhds
          (pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T)) := by
    -- Proof comment: add the convergent `X dY` sums and the convergent bracket sums termwise.
    exact (hItoXY.tendsto T).add (HasQuadraticCovariationAlong.tendsto_partition_sum hcovXY T)
  have hreverse :
      Tendsto
        (fun n ↦
          X T * Y T - X 0 * Y 0 -
            (partitionPathwiseItoApproximationUpTo X Y dyadicPartitionSequence T n +
              partitionQuadraticCovariationSum dyadicPartitionSequence X Y T n))
        atTop
        (nhds
          (X T * Y T - X 0 * Y 0 -
            (pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T))) := by
    -- Proof comment: subtract the convergent deterministic-plus-bracket term from the constant
    -- endpoint product term.
    exact tendsto_const_nhds.sub hsum
  -- Proof comment: rewrite the left-hand side through the finite-row product decomposition.
  convert hreverse using 1
  ext n
  simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
    dyadicProductRowDecomposition X Y T n

-- Proof sketch: rewrite the `Y dX` row by the finite dyadic product decomposition, compare its
-- two limits, and rearrange the resulting scalar identity.
/-- For a chosen continuous dyadic quadratic covariation path `⟨X,Y⟩`, the dyadic pathwise
product rule takes the canonical form
`X_T Y_T = X_0 Y_0 + ∫_0^T Y_s dX_s + ∫_0^T X_s dY_s + ⟨X,Y⟩_T`,
where the Itô terms are expressed by `pathwiseItoIntegralAlong`. -/
theorem dyadic_pathwise_product_rule
    {X Y : PathSpace}
    (covXY : PathSpace)
    (hcovXY : HasQuadraticCovariationAlong X Y covXY)
    (hItoYX :
      HasPathwiseItoIntegralAlong
        Y
        X
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong Y X dyadicPartitionSequence))
    (hItoXY :
      HasPathwiseItoIntegralAlong
        X
        Y
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong X Y dyadicPartitionSequence))
    (T : NNReal) :
    X T * Y T =
      X 0 * Y 0 +
        pathwiseItoIntegralAlong Y X dyadicPartitionSequence T +
        pathwiseItoIntegralAlong X Y dyadicPartitionSequence T +
        covXY T := by
  have hswap :
      HasPathwiseItoIntegralAlong
        Y
        X
        dyadicPartitionSequence
        (fun T ↦
          X T * Y T - X 0 * Y 0 -
            (pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T)) :=
    hasPathwiseItoIntegralAlong_swap_of_quadraticCovariation hItoXY covXY hcovXY
  have hlimit :
      pathwiseItoIntegralAlong Y X dyadicPartitionSequence T =
        X T * Y T - X 0 * Y 0 -
          (pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T) :=
    tendsto_nhds_unique (hItoYX.tendsto T) (hswap.tendsto T)
  -- Proof comment: rearrange the limit identity into the textbook product rule.
  have hfinal :
      X T * Y T =
        X 0 * Y 0 +
          (pathwiseItoIntegralAlong Y X dyadicPartitionSequence T +
            pathwiseItoIntegralAlong X Y dyadicPartitionSequence T + covXY T) := by
    linarith
  simpa [add_assoc, add_left_comm, add_comm] using hfinal

/-- Corollary 25.32: if `X - Y` and `X + Y` lie in `𝒞_qv`, then the dyadic quadratic covariation
`⟨X,Y⟩` is available by polarization, and whenever the canonical dyadic pathwise Itô integrals of
`Y` against `X` and of `X` against `Y` satisfy their defining convergence, the product rule
`X_T Y_T = X_0 Y_0 + ∫_0^T Y_s dX_s + ∫_0^T X_s dY_s + ⟨X,Y⟩_T`
holds for every `T ≥ 0`, with the Itô terms written via the canonical owner
`pathwiseItoIntegralAlong`. -/
theorem dyadic_pathwise_product_rule_of_continuous_square_variation
    {X Y : PathSpace}
    (hXmY : HasContinuousSquareVariation (X - Y))
    (hXpY : HasContinuousSquareVariation (X + Y))
    (hItoYX :
      HasPathwiseItoIntegralAlong
        Y
        X
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong Y X dyadicPartitionSequence))
    (hItoXY :
      HasPathwiseItoIntegralAlong
        X
        Y
        dyadicPartitionSequence
        (pathwiseItoIntegralAlong X Y dyadicPartitionSequence))
    (T : NNReal) :
    ∃ covXY : PathSpace,
      HasQuadraticCovariationAlong X Y covXY ∧
        X T * Y T =
          X 0 * Y 0 +
            pathwiseItoIntegralAlong Y X dyadicPartitionSequence T +
            pathwiseItoIntegralAlong X Y dyadicPartitionSequence T +
            covXY T := by
  obtain ⟨covXY, hcovXY⟩ :=
    exists_quadratic_covariation_along_of_hasContinuousSquareVariation hXmY hXpY
  exact ⟨covXY, hcovXY,
    dyadic_pathwise_product_rule covXY hcovXY hItoYX hItoXY T⟩
