/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_58
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_54Support
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Remark_21_62
import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_25

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ
local notation "dyadicPartitionSequence" => Definition2158.dyadicPartitionSequence

/-- Helper for Theorem 25.30: the weighted quadratic partition sum of a scalar path on `[0, T]`
along the `n`-th dyadic row. -/
def pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2

/-- Helper for Theorem 25.30: unfolding
`pathwiseWeightedPartitionQuadraticVariationApproximationUpTo` exposes the defining weighted sum. -/
@[simp] theorem pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def
    (f : NNReal → ℝ) (X : NNReal → ℝ) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (T : NNReal) (n : ℕ) :
    pathwiseWeightedPartitionQuadraticVariationApproximationUpTo f X P T n =
      Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
        f (P n k) * (X (partitionNextPointUpTo P n k T) - X (P n k)) ^ 2 := rfl

/-- Helper for Theorem 25.30: every partition point that contributes to the truncated sum up to
`T` lies strictly before `T`. -/
lemma partitionPoint_lt_time_of_lt_truncationBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k < T := by
  have hk_not : ¬ T ≤ P n k := by
    intro hkT
    have hmin : partitionBoundIndex P n T ≤ k := by
      simpa [partitionBoundIndex] using
        (Nat.find_min' (exists_partition_index_le_time P n T) hkT)
    exact (not_le_of_gt hk) hmin
  exact lt_of_not_ge hk_not

/-- Helper for Theorem 25.30: every partition point that contributes to the truncated sum up to
`T` belongs to `Set.Icc 0 T`. -/
lemma partitionPoint_mem_Icc_of_lt_truncationBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    P n k ∈ Set.Icc 0 T := by
  constructor
  · exact bot_le
  · exact le_of_lt (partitionPoint_lt_time_of_lt_truncationBoundIndex P n k T hk)

/-- Helper for Theorem 25.30: every clipped interval from `P n k` to
`partitionNextPointUpTo P n k T` still lies in `Set.Icc 0 T`. -/
theorem partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (_hk : k < partitionBoundIndex P n T) :
    partitionNextPointUpTo P n k T ∈ Set.Icc 0 T := by
  -- The clipped successor is the minimum of the next partition point and `T`.
  constructor
  · exact bot_le
  · simp [partitionNextPointUpTo]

/-- Helper for Theorem 25.30: every clipped interval from `P n k` to
`partitionNextPointUpTo P n k T` has size at most one mesh width. -/
lemma edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (n k : ℕ) (T : NNReal) (hk : k < partitionBoundIndex P n T) :
    edist (P n k) (partitionNextPointUpTo P n k T) ≤ partitionMesh P n := by
  have hleft : P n k ≤ partitionNextPointUpTo P n k T := by
    rw [partitionNextPointUpTo]
    refine le_min ?_ ?_
    · exact le_of_lt ((instStrictMono_of_isAdmissiblePartitionSequence (P := P) n)
        (Nat.lt_succ_self k))
    · exact (partitionPoint_mem_Icc_of_lt_truncationBoundIndex P n k T hk).2
  have hright : partitionNextPointUpTo P n k T ≤ P n (k + 1) := by
    rw [partitionNextPointUpTo]
    exact min_le_left _ _
  have hdist :
      edist (P n k) (partitionNextPointUpTo P n k T) ≤ edist (P n k) (P n (k + 1)) := by
    have hsucc : P n k < P n (k + 1) := by
      exact (instStrictMono_of_isAdmissiblePartitionSequence (P := P) n) (Nat.lt_succ_self k)
    rw [edist_nndist, edist_nndist, NNReal.nndist_eq, NNReal.nndist_eq,
      tsub_eq_zero_of_le hleft, tsub_eq_zero_of_le (le_of_lt hsucc), max_eq_right, max_eq_right]
    · exact_mod_cast tsub_le_tsub_right hright _
    · simp
    · simp
  calc
    edist (P n k) (partitionNextPointUpTo P n k T)
        ≤ edist (P n k) (P n (k + 1)) := hdist
    _ ≤ partitionMesh P n := by
      rw [partitionMesh]
      exact le_iSup (fun j ↦ edist (P n j) (P n (j + 1))) k

/-- The dyadic left-point sum approximating the integral of `H` against the quadratic
covariation of `F` and `G` on `[0, T]`. -/
noncomputable def dyadicQuadraticCovariationIntegralApproximationUpTo
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
    H (dyadicPartitionSequence n k) *
      (F (partitionNextPointUpTo dyadicPartitionSequence n k T) - F (dyadicPartitionSequence n k)) *
      (G (partitionNextPointUpTo dyadicPartitionSequence n k T) - G (dyadicPartitionSequence n k))

/-- Expanding `dyadicQuadraticCovariationIntegralApproximationUpTo` gives the defining dyadic
left-point sum on `[0, T]`. -/
theorem dyadicQuadraticCovariationIntegralApproximationUpTo_def
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadicQuadraticCovariationIntegralApproximationUpTo H F G T n =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
        H (dyadicPartitionSequence n k) *
          (F (partitionNextPointUpTo dyadicPartitionSequence n k T) -
            F (dyadicPartitionSequence n k)) *
          (G (partitionNextPointUpTo dyadicPartitionSequence n k T) -
            G (dyadicPartitionSequence n k)) := rfl

/-- The canonical dyadic pathwise integral of `H` against the quadratic covariation of `F` and
`G` is the process obtained by taking the `limUnder` of the left-point mixed-increment sums at
each horizon `T`. -/
noncomputable def pathwiseQuadraticCovariationIntegral
    (H : NNReal → ℝ) (F G : PathSpace) : PathwiseProcess :=
  fun T ↦ limUnder atTop (dyadicQuadraticCovariationIntegralApproximationUpTo H F G T)

/-- Evaluating `pathwiseQuadraticCovariationIntegral` gives the `limUnder` of the dyadic
left-point mixed-increment sums at horizon `T`. -/
theorem pathwiseQuadraticCovariationIntegral_def
    (H : NNReal → ℝ) (F G : PathSpace) (T : NNReal) :
    pathwiseQuadraticCovariationIntegral H F G T =
      limUnder atTop (dyadicQuadraticCovariationIntegralApproximationUpTo H F G T) := rfl

/-- Helper for Theorem 25.30: any concrete limit of the weighted dyadic mixed sums identifies the
canonical pathwise quadratic-covariation integral at the fixed horizon `T`. -/
theorem pathwiseQuadraticCovariationIntegral_eq_of_tendsto
    (H : NNReal → ℝ) (Y Z : PathSpace) (T : NNReal) {L : ℝ}
    (hlim :
      Tendsto
        (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
        atTop
        (nhds L)) :
    pathwiseQuadraticCovariationIntegral H Y Z T = L := by
  -- Unfold the canonical integral and rewrite the `limUnder` through the genuine limit `hlim`.
  rw [pathwiseQuadraticCovariationIntegral_def, hlim.limUnder_eq]

/-- Helper for Theorem 25.30: the dyadic square variation of `F + G` expands into the `F`,
mixed, and `G` contributions. -/
private theorem dyadicSquareVariationSum_add_eq
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (F + G) T n =
      dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
        dyadic_p_variation_sum 2 G T n := by
  let N := partitionBoundIndex dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo dyadicPartitionSequence n k T) -
      F (dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo dyadicPartitionSequence n k T) -
      G (dyadicPartitionSequence n k)
  -- Proof comment: expand every dyadic increment of `F + G` and regroup the resulting finite sum
  -- into the pure `F`, mixed, and pure `G` parts.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((F + G) (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
                ((F + G) (dyadicPartitionSequence n k))|)
            2) =
      Finset.sum (Finset.range N) (fun k ↦ (ΔF k + ΔG k) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [← Real.rpow_natCast]
        have hadd :
            (F (partitionNextPointUpTo dyadicPartitionSequence n k T) +
                G (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
              (F (dyadicPartitionSequence n k) + G (dyadicPartitionSequence n k)) =
            ΔF k + ΔG k := by
          dsimp [ΔF, ΔG]
          ring
        rw [ContinuousMap.add_apply, ContinuousMap.add_apply, hadd]
        simp [sq_abs]
    _ = Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2 + 2 * (ΔF k * ΔG k) + (ΔG k) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) +
          2 * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.mul_sum]
    _ = dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
          dyadic_p_variation_sum 2 G T n := by
        simp [N, ΔF, ΔG, dyadic_p_variation_sum, dyadic_quadratic_covariation_sum,
          partitionPVariationSum, partitionQuadraticCovariationSum, sq_abs]

/-- Helper for Theorem 25.30: the dyadic square variation of `F - G` expands into the `F`,
mixed, and `G` contributions with the mixed term carrying the opposite sign. -/
private theorem dyadicSquareVariationSum_sub_eq
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    dyadic_p_variation_sum 2 (F - G) T n =
      dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
        dyadic_p_variation_sum 2 G T n := by
  let N := partitionBoundIndex dyadicPartitionSequence n T
  let ΔF : ℕ → ℝ := fun k ↦
    F (partitionNextPointUpTo dyadicPartitionSequence n k T) -
      F (dyadicPartitionSequence n k)
  let ΔG : ℕ → ℝ := fun k ↦
    G (partitionNextPointUpTo dyadicPartitionSequence n k T) -
      G (dyadicPartitionSequence n k)
  -- Proof comment: expand every dyadic increment of `F - G` and regroup the finite sum so that
  -- the mixed quadratic-covariation term appears with a minus sign.
  rw [dyadic_p_variation_sum, partitionPVariationSum]
  calc
    Finset.sum (Finset.range N)
        (fun k ↦
          Real.rpow
            (|((F - G) (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
                ((F - G) (dyadicPartitionSequence n k))|)
            2) =
      Finset.sum (Finset.range N) (fun k ↦ (ΔF k - ΔG k) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        rw [← Real.rpow_natCast]
        have hsub :
            (F (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                G (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
              (F (dyadicPartitionSequence n k) - G (dyadicPartitionSequence n k)) =
            ΔF k - ΔG k := by
          dsimp [ΔF, ΔG]
          ring
        rw [ContinuousMap.sub_apply, ContinuousMap.sub_apply, hsub]
        simp [sq_abs]
    _ = Finset.sum (Finset.range N)
          (fun k ↦ (ΔF k) ^ 2 - 2 * (ΔF k * ΔG k) + (ΔG k) ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        ring
    _ = Finset.sum (Finset.range N) (fun k ↦ (ΔF k) ^ 2 - 2 * (ΔF k * ΔG k)) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
        rw [Finset.sum_add_distrib]
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) -
          Finset.sum (Finset.range N) (fun k ↦ 2 * (ΔF k * ΔG k)) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
        rw [Finset.sum_sub_distrib]
    _ = (Finset.sum (Finset.range N) fun k ↦ (ΔF k) ^ 2) -
          2 * Finset.sum (Finset.range N) (fun k ↦ ΔF k * ΔG k) +
          Finset.sum (Finset.range N) (fun k ↦ (ΔG k) ^ 2) := by
        rw [Finset.mul_sum]
    _ = dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
          dyadic_p_variation_sum 2 G T n := by
        simp [N, ΔF, ΔG, dyadic_p_variation_sum, dyadic_quadratic_covariation_sum,
          partitionPVariationSum, partitionQuadraticCovariationSum, sq_abs]

/-- Helper for Theorem 25.30: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F + G`. -/
private theorem hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG) :
    HasSquareVariationAlong (F + G) (fun T ↦ brF T + 2 * covFG T + brG T) := by
  intro T
  have hFsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  have hGsum := HasSquareVariationAlong.tendsto_partition_sum hG T
  have hFGsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the dyadic square sum of `F + G` into the sum of the three dyadic
  -- limits and then pass to the limit termwise.
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n + 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (brF T + 2 * covFG T + brG T)) := by
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using
      hFsum.add ((hFGsum.const_mul 2).add hGsum)
  convert hsum using 1
  ext n
  simpa [dyadic_p_variation_sum] using dyadicSquareVariationSum_add_eq F G T n

/-- Helper for Theorem 25.30: square-variation witnesses for `F`, `G`, and their quadratic
covariation combine into the canonical square-variation witness for `F - G`. -/
private theorem hasSquareVariationAlong_sub_of_hasQuadraticCovariationAlong
    {F G : PathSpace} {brF brG covFG : PathwiseProcess}
    (hF : HasSquareVariationAlong F brF)
    (hG : HasSquareVariationAlong G brG)
    (hFG : HasQuadraticCovariationAlong F G covFG) :
    HasSquareVariationAlong (F - G) (fun T ↦ brF T - 2 * covFG T + brG T) := by
  intro T
  have hFsum := HasSquareVariationAlong.tendsto_partition_sum hF T
  have hGsum := HasSquareVariationAlong.tendsto_partition_sum hG T
  have hFGsum := HasQuadraticCovariationAlong.tendsto_partition_sum hFG T
  -- Proof comment: rewrite the dyadic square sum of `F - G` into the same three dyadic limits
  -- with the mixed term carrying the opposite sign.
  have hsum :
      Tendsto
        (fun n ↦
          dyadic_p_variation_sum 2 F T n - 2 * dyadic_quadratic_covariation_sum F G T n +
            dyadic_p_variation_sum 2 G T n)
        atTop
        (nhds (brF T - 2 * covFG T + brG T)) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
      mul_comm] using
      (hFsum.sub (hFGsum.const_mul 2)).add hGsum
  convert hsum using 1
  ext n
  simpa [dyadic_p_variation_sum] using dyadicSquareVariationSum_sub_eq F G T n

/-- The canonical Euclidean model of a continuous `d`-dimensional path on `[0,∞)`. -/
abbrev VectorPathSpace (d : ℕ) := C(NNReal, EuclideanSpace ℝ (Fin d))

variable {d : ℕ}

local notation "State" => EuclideanSpace ℝ (Fin d)
local notation "StateCoords" => (EuclideanSpace.equiv (Fin d) ℝ : State ≃L[ℝ] Fin d → ℝ)

/-- The `i`-th real-valued coordinate path of a continuous vector-valued path. -/
abbrev vectorPathComponent (X : VectorPathSpace d) (i : Fin d) : PathSpace :=
  { toFun := fun t ↦ X t i
    continuous_toFun := by
      have hX : Continuous fun t ↦ StateCoords (X t) :=
        (StateCoords : State →L[ℝ] Fin d → ℝ).continuous.comp X.continuous
      simpa using (continuous_apply i).comp hX }

-- Proof sketch: unfold `vectorPathComponent`; it is the continuous map whose underlying function
-- evaluates `X` in the coordinate `i`.
/-- Evaluating `vectorPathComponent X i` at time `t` returns the `i`-th coordinate `X t i`. -/
theorem vectorPathComponent_apply
    (X : VectorPathSpace d) (i : Fin d) (t : NNReal) :
    vectorPathComponent X i t = X t i := rfl

/-- The primitive dyadic quadratic-covariation owner property for a continuous
`d`-dimensional path. -/
def HasContinuousQuadraticCovariations (X : VectorPathSpace d) : Prop :=
  ∀ i j : Fin d,
    ∃ cov : PathSpace,
      HasQuadraticCovariationAlong
        (vectorPathComponent X i)
        (vectorPathComponent X j)
        cov

/-- The textbook class `𝒞_qv^d` of continuous `d`-dimensional paths whose coordinate pairs admit
dyadic quadratic covariations represented by continuous paths. -/
abbrev ContinuousQuadraticCovariationClass (d : ℕ) : Set (VectorPathSpace d) :=
  HasContinuousQuadraticCovariations

notation "𝒞_qv^" d => ContinuousQuadraticCovariationClass d

/- Membership in `𝒞_qv^d` is the source-facing set-level view of the primitive owner property
`HasContinuousQuadraticCovariations`. -/
theorem mem_𝒞_qv_d_iff (X : VectorPathSpace d) :
    X ∈ (𝒞_qv^d) ↔ HasContinuousQuadraticCovariations X :=
  Iff.rfl

/-- Membership in `𝒞_qv^d` is equivalent to choosing a continuous dyadic quadratic-covariation
path for each coordinate pair. -/
theorem mem_𝒞_qv_d_iff_exists_family
    (X : VectorPathSpace d) :
    X ∈ (𝒞_qv^d) ↔
      ∃ cov : Fin d → Fin d → PathSpace,
        ∀ i j : Fin d,
          HasQuadraticCovariationAlong
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            (cov i j) := by
  constructor
  · intro hX
    classical
    choose cov hcov using hX
    exact ⟨cov, hcov⟩
  · rintro ⟨cov, hcov⟩ i j
    exact ⟨cov i j, hcov i j⟩

/-- The partial derivative `∂ᵢF` computed by varying only the `i`-th coordinate. -/
noncomputable def partialDeriv
    (F : State → ℝ) (i : Fin d) : State → ℝ :=
  fun x ↦ deriv (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) (x i)

notation:max "∂[" i "] " F:arg => partialDeriv F i

-- Proof sketch: unfold `partialDeriv`; the derivative is taken along the coordinate line obtained
-- by varying only the `i`-th Euclidean coordinate of `x`.
/-- Evaluating `(∂[i] F)` at `x` gives the one-variable derivative along the `i`-th
coordinate line through `x`. -/
theorem partialDeriv_def
    (F : State → ℝ) (i : Fin d) (x : State) :
    (∂[i] F) x =
      deriv (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) (x i) := rfl

/-- The mixed second partial derivative `∂ⱼ∂ᵢF` computed by iterating coordinate derivatives. -/
noncomputable def secondPartialDeriv
    (F : State → ℝ) (i j : Fin d) : State → ℝ :=
  fun x ↦ deriv (fun t ↦ (∂[i] F) (x + EuclideanSpace.single j (t - x j))) (x j)

notation:max "∂²[" i "," j "] " F:arg => secondPartialDeriv F i j

-- Proof sketch: unfold `secondPartialDeriv`; it differentiates the `i`-th partial derivative of
-- `F` along the `j`-th coordinate line through `x`.
/-- Evaluating `(∂²[i, j] F)` at `x` gives the iterated coordinate derivative
`∂ⱼ∂ᵢF(x)`. -/
theorem secondPartialDeriv_def
    (F : State → ℝ) (i j : Fin d) (x : State) :
    (∂²[i, j] F) x =
      deriv (fun t ↦ (∂[i] F) (x + EuclideanSpace.single j (t - x j))) (x j) := rfl

/-- Helper for Theorem 25.30: a point on the `i`-th coordinate line through `x` really has
`i`-th coordinate `t`. -/
private theorem point_on_coordinateLine_apply
    (x : State) (i : Fin d) (t : ℝ) :
    (x + EuclideanSpace.single i (t - x i)) i = t := by
  -- Evaluating the coordinate-line point at `i` collapses the inserted displacement.
  simp

/-- Helper for Theorem 25.30: moving twice along the same coordinate line is the same as moving
directly to the final point. -/
private theorem coordinateLine_compose_self
    (x : State) (i : Fin d) (t u : ℝ) :
    x + EuclideanSpace.single i (t - x i) +
        EuclideanSpace.single i (u - (x + EuclideanSpace.single i (t - x i)) i) =
      x + EuclideanSpace.single i (u - x i) := by
  -- Compare coordinates: only the `i`-th coordinate changes, and there the increments add.
  ext j
  by_cases h : j = i
  · subst h
    simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  · simp [h]

/-- Helper for Theorem 25.30: the coordinate partial derivative `∂[i] F` is the Fréchet
derivative of `F` applied to the `i`-th basis vector. -/
theorem partialDeriv_eq_fderiv_apply
    (F : State → ℝ) (hF : Differentiable ℝ F) (i : Fin d) :
    ∂[i] F = fun x ↦ (fderiv ℝ F x) (EuclideanSpace.single i (1 : ℝ)) := by
  funext x
  let e : State := EuclideanSpace.single i (1 : ℝ)
  let g : ℝ → ℝ := fun s ↦ F (x + s • e)
  have hg :
      (fun t ↦ F (x + EuclideanSpace.single i (t - x i))) =
        fun t ↦ g (t - x i) := by
    -- Recenter the coordinate derivative around the origin on the `i`-th axis.
    funext t
    have haxis :
        x + EuclideanSpace.single i (t - x i) = x + (t - x i) • e := by
      ext j
      by_cases h : j = i
      · subst h
        simp [e, sub_eq_add_neg]
      · simp [e, h]
    simpa [g] using congrArg F haxis
  have hline : deriv g 0 = (fderiv ℝ F x) e := by
    -- The shifted axis curve is exactly the line derivative of `F` at `x` in direction `e_i`.
    simpa [g, e, lineDeriv] using
      ((hF x).lineDeriv_eq_fderiv (v := e))
  -- Shift the derivative back from `x i` to `0` and apply the line-derivative formula.
  rw [partialDeriv_def, hg, deriv_comp_sub_const]
  simpa [e] using hline

/-- Helper for Theorem 25.30: the mixed coordinate derivative `∂²[i, j] F` is the Fréchet
derivative of `∂[i] F` applied to the `j`-th basis vector. -/
theorem secondPartialDeriv_eq_fderiv_apply
    (F : State → ℝ) (i j : Fin d) (hFi : Differentiable ℝ (partialDeriv F i)) :
    ∂²[i, j] F = fun x ↦ (fderiv ℝ (∂[i] F) x) (EuclideanSpace.single j (1 : ℝ)) := by
  let G : State → ℝ := ∂[i] F
  have hG : Differentiable ℝ G := by
    dsimp [G]
    exact hFi
  -- Reuse the first-derivative bridge on the function `∂[i] F`.
  simpa [G, secondPartialDeriv] using
    (partialDeriv_eq_fderiv_apply (F := G) (i := j) hG)

/-- Helper for Theorem 25.30: a `C²` map has differentiable coordinate partial derivatives. -/
private theorem differentiable_partialDeriv
    (F : State → ℝ) (hf : ContDiff ℝ 2 F) (i : Fin d) :
    Differentiable ℝ (∂[i] F) := by
  let ei : State := EuclideanSpace.single i (1 : ℝ)
  -- Proof comment: rewrite `∂[i] F` as the Fréchet derivative of `F` applied to the basis vector
  -- `eᵢ`, then use the `C²` regularity of `F`.
  have hfd :
      ContDiff ℝ 1 (fun x ↦ (fderiv ℝ F x) ei) := by
    simpa [ei] using
      ((contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := State) (E := ℝ) (n := 1)
        (f := F)).mp hf).2.2 ei
  simpa [partialDeriv_eq_fderiv_apply F (hf.differentiable (by norm_num)) i] using
    hfd.differentiable_one

/-- Helper for Theorem 25.30: the derivative of `s ↦ F (x + s • δ)` is the coordinate gradient
pairing `∑ᵢ ∂ᵢF(x + sδ) δᵢ`. -/
private theorem lineDeriv_eq_sum_partialDeriv_mul
    (F : State → ℝ) (hF : Differentiable ℝ F) (x δ : State) (s : ℝ) :
    deriv (fun u : ℝ ↦ F (x + u • δ)) s =
      ∑ i : Fin d, (∂[i] F) (x + s • δ) * δ i := by
  let g : ℝ → ℝ := fun u ↦ F (x + u • δ)
  have hshift :
      deriv g s = deriv (fun u : ℝ ↦ F ((x + s • δ) + u • δ)) 0 := by
    -- Shift the line derivative to the origin so the `lineDeriv` API applies directly.
    simpa [g, add_assoc, add_left_comm, add_comm, add_smul] using
      (deriv_comp_const_add (f := g) s 0).symm
  have hline :
      deriv (fun u : ℝ ↦ F ((x + s • δ) + u • δ)) 0 =
        (fderiv ℝ F (x + s • δ)) δ := by
    -- The shifted one-variable derivative is the Fréchet derivative along the direction `δ`.
    simpa [lineDeriv] using
      ((hF (x + s • δ)).lineDeriv_eq_fderiv (v := δ))
  have hδ :
      δ = ∑ i : Fin d, δ i • EuclideanSpace.single i (1 : ℝ) := by
    -- Expand the direction vector in the standard Euclidean basis.
    simpa [EuclideanSpace.basisFun_apply] using
      ((EuclideanSpace.basisFun (Fin d) ℝ).sum_repr δ).symm
  calc
    deriv (fun u : ℝ ↦ F (x + u • δ)) s = (fderiv ℝ F (x + s • δ)) δ := by
      exact hshift.trans hline
    _ =
        (fderiv ℝ F (x + s • δ))
          (∑ i : Fin d, δ i • EuclideanSpace.single i (1 : ℝ)) := by
      exact congrArg (fun v : State ↦ (fderiv ℝ F (x + s • δ)) v) hδ
    _ =
        ∑ i : Fin d,
          (fderiv ℝ F (x + s • δ)) (δ i • EuclideanSpace.single i (1 : ℝ)) := by
      rw [map_sum]
    _ = ∑ i : Fin d, δ i * (fderiv ℝ F (x + s • δ)) (EuclideanSpace.single i (1 : ℝ)) := by
      simp [map_smul, smul_eq_mul]
    _ = ∑ i : Fin d, (∂[i] F) (x + s • δ) * δ i := by
      -- Rewrite each Fréchet derivative entry back to the corresponding coordinate derivative.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [partialDeriv_eq_fderiv_apply F hF i]
      ring

/-- Helper for Theorem 25.30: the second line derivative of `F` along `δ` is the coordinate
Hessian pairing `∑ᵢ ∑ⱼ ∂ⱼ∂ᵢF(x + sδ) δᵢ δⱼ`. -/
private theorem lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul
    (F : State → ℝ) (hf : ContDiff ℝ 2 F) (x δ : State) (s : ℝ) :
    iteratedDeriv 2 (fun u : ℝ ↦ F (x + u • δ)) s =
      ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] F) (x + s • δ) * δ i * δ j := by
  have hDiffLine (i : Fin d) :
      DifferentiableAt ℝ (fun u : ℝ ↦ (∂[i] F) (x + u • δ)) s := by
    -- Compose the differentiable coordinate derivative with the affine line `u ↦ x + uδ`.
    exact DifferentiableAt.comp s
      ((differentiable_partialDeriv F hf i) (x + s • δ))
      ((differentiableAt_id.smul_const δ).const_add x)
  have hLinePartial (i : Fin d) :
      deriv (fun u : ℝ ↦ (∂[i] F) (x + u • δ)) s =
        ∑ j : Fin d, (∂²[i, j] F) (x + s • δ) * δ j := by
    -- Apply the first line-derivative formula to the function `∂[i] F`.
    simpa [secondPartialDeriv] using
      (lineDeriv_eq_sum_partialDeriv_mul (F := ∂[i] F)
        (differentiable_partialDeriv F hf i) x δ s)
  calc
    iteratedDeriv 2 (fun u : ℝ ↦ F (x + u • δ)) s =
        deriv (fun u : ℝ ↦ ∑ i : Fin d, (∂[i] F) (x + u • δ) * δ i) s := by
      -- First rewrite the first line derivative into the coordinate-gradient expansion.
      rw [iteratedDeriv_succ, iteratedDeriv_one]
      congr 1
      funext u
      exact lineDeriv_eq_sum_partialDeriv_mul F (hf.differentiable (by norm_num)) x δ u
    _ =
        ∑ i : Fin d, deriv (fun u : ℝ ↦ (∂[i] F) (x + u • δ) * δ i) s := by
      -- Differentiate the finite sum termwise.
      rw [deriv_fun_sum]
      intro i hi
      exact (hDiffLine i).mul_const (δ i)
    _ =
        ∑ i : Fin d, (∑ j : Fin d, (∂²[i, j] F) (x + s • δ) * δ j) * δ i := by
      -- Each summand differentiates by the already-normalized first-order formula.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [deriv_mul_const (hDiffLine i), hLinePartial i]
    _ = ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] F) (x + s • δ) * δ i * δ j := by
      -- Reassociate the scalar factors into the stated Hessian pairing.
      refine Finset.sum_congr rfl ?_
      intro i hi
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl ?_
      intro j hj
      ring

/-- Helper for Theorem 25.30: for `F ∈ C²(ℝᵈ)`, every Hessian entry `x ↦ ∂²[i, j] F x` is
continuous. -/
theorem continuous_secondPartialDeriv
    (F : State → ℝ) (hf : ContDiff ℝ 2 F) (i j : Fin d) :
    Continuous (∂²[i, j] F) := by
  let ei : State := EuclideanSpace.single i (1 : ℝ)
  have hpartialContDiff :
      ContDiff ℝ 1 (∂[i] F) := by
    -- Rewrite `∂[i] F` as the Fréchet derivative of `F` applied to the basis vector `eᵢ`.
    have hfd :
        ContDiff ℝ 1 (fun x ↦ (fderiv ℝ F x) ei) := by
      simpa [ei] using
        ((contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := State) (E := ℝ) (n := 1)
          (f := F)).mp hf).2.2 ei
    simpa [partialDeriv_eq_fderiv_apply F (hf.differentiable (by norm_num)) i] using hfd
  have happly :
      ContDiff ℝ 0 (fun x ↦ (fderiv ℝ (∂[i] F) x) (EuclideanSpace.single j (1 : ℝ))) := by
    -- The Fréchet derivative of `∂[i] F` applied to a fixed basis vector is continuous.
    simpa using
      ((contDiff_succ_iff_fderiv_apply (𝕜 := ℝ) (D := State) (E := ℝ) (n := 0)
        (f := ∂[i] F)).mp hpartialContDiff).2.2 (EuclideanSpace.single j (1 : ℝ))
  -- Rewriting through the second-partial/Frechet-derivative bridge yields the target continuity.
  simpa [secondPartialDeriv_eq_fderiv_apply F i j (differentiable_partialDeriv F hf i)] using
    happly.continuous

/-- The dyadic left-point Riemann sum for the pathwise multidimensional Itô integral of `∇F(X)`
on `[0,T]`. -/
noncomputable def dyadicMultidimensionalItoApproximationUpTo
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
    ∑ i : Fin d,
      (∂[i] F) (X (dyadicPartitionSequence n k)) *
        (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
          X (dyadicPartitionSequence n k) i)

-- Proof sketch: unfold `dyadicMultidimensionalItoApproximationUpTo`; this is exactly the finite
-- sum of the coordinate partial derivatives at the left endpoints against the coordinate
-- increments along the dyadic partition of `[0,T]`.
/-- Expanding `dyadicMultidimensionalItoApproximationUpTo` gives the dyadic left-point gradient
sum on `[0,T]`. -/
theorem dyadicMultidimensionalItoApproximationUpTo_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoApproximationUpTo F X T n =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
        ∑ i : Fin d,
          (∂[i] F) (X (dyadicPartitionSequence n k)) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
              X (dyadicPartitionSequence n k) i) := rfl

/-- The dyadic second-order correction sum in the multidimensional pathwise Itô formula on
`[0,T]`. -/
noncomputable def dyadicMultidimensionalItoCorrectionApproximationUpTo
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  (1 / 2 : ℝ) *
    Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
      ∑ i : Fin d, ∑ j : Fin d,
          (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
              X (dyadicPartitionSequence n k) i) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
              X (dyadicPartitionSequence n k) j)

-- Proof sketch: unfold
-- `dyadicMultidimensionalItoCorrectionApproximationUpTo`; this is exactly the finite second-order
-- Taylor correction sum along the dyadic partition of `[0,T]`.
/-- Expanding `dyadicMultidimensionalItoCorrectionApproximationUpTo` gives the dyadic second-order
correction sum on `[0,T]`. -/
theorem dyadicMultidimensionalItoCorrectionApproximationUpTo_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n =
      (1 / 2 : ℝ) *
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
          ∑ i : Fin d, ∑ j : Fin d,
              (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
                  X (dyadicPartitionSequence n k) i) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
                  X (dyadicPartitionSequence n k) j) := rfl

/-- The pathwise multidimensional Itô integral is the process obtained from the `limUnder` of the
dyadic left-point sums. -/
noncomputable def pathwiseMultidimensionalItoIntegral
    (F : State → ℝ) (X : VectorPathSpace d) : PathwiseProcess :=
  fun T ↦ limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T)

-- Proof sketch: unfold `pathwiseMultidimensionalItoIntegral`; by definition it is the `limUnder`
-- of the dyadic multidimensional Itô approximations.
/-- Evaluating `pathwiseMultidimensionalItoIntegral` gives the `limUnder` of the dyadic
multidimensional Itô sums. -/
theorem pathwiseMultidimensionalItoIntegral_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) :
    pathwiseMultidimensionalItoIntegral F X T =
      limUnder atTop (dyadicMultidimensionalItoApproximationUpTo F X T) := rfl

/-- Helper for Theorem 25.30: any concrete limit of the dyadic multidimensional Itô sums
identifies the canonical pathwise multidimensional Itô integral at the fixed horizon `T`. -/
theorem pathwiseMultidimensionalItoIntegral_eq_of_tendsto
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) {L : ℝ}
    (hlim :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n)
        atTop
        (nhds L)) :
    pathwiseMultidimensionalItoIntegral F X T = L := by
  -- Unfold the canonical integral and rewrite the `limUnder` through the genuine limit `hlim`.
  rw [pathwiseMultidimensionalItoIntegral_def, hlim.limUnder_eq]

/-- The quadratic correction in the multidimensional pathwise Itô formula is the sum of the
pairwise pathwise quadratic-covariation integrals of the Hessian entries. -/
noncomputable def pathwiseMultidimensionalItoCorrection
    (F : State → ℝ) (X : VectorPathSpace d) : PathwiseProcess :=
  fun T ↦
    (1 / 2 : ℝ) *
      ∑ i : Fin d, ∑ j : Fin d,
          pathwiseQuadraticCovariationIntegral
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T

-- Proof sketch: unfold `pathwiseMultidimensionalItoCorrection`; by definition it is the finite
-- sum of the pairwise pathwise quadratic-covariation integrals of the Hessian entries.
/-- Expanding `pathwiseMultidimensionalItoCorrection` gives the sum of the pairwise pathwise
quadratic-covariation integrals of the Hessian entries. -/
theorem pathwiseMultidimensionalItoCorrection_def
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) :
    pathwiseMultidimensionalItoCorrection F X T =
      (1 / 2 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
            pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[i, j] F) (X s))
              (vectorPathComponent X i)
              (vectorPathComponent X j)
              T := rfl

/-- Helper for Theorem 25.30: the dyadic multidimensional correction is the finite sum of the
pairwise weighted dyadic quadratic-covariation approximations. -/
theorem dyadicMultidimensionalItoCorrectionApproximationUpTo_eq_sum_covariationApproximations
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n =
      (1 / 2 : ℝ) *
        ∑ i : Fin d, ∑ j : Fin d,
          dyadicQuadraticCovariationIntegralApproximationUpTo
            (fun s ↦ (∂²[i, j] F) (X s))
            (vectorPathComponent X i)
            (vectorPathComponent X j)
            T
            n := by
  -- Expand both named approximations to the common mixed-increment summand.
  rw [dyadicMultidimensionalItoCorrectionApproximationUpTo_def]
  simp_rw [dyadicQuadraticCovariationIntegralApproximationUpTo_def, vectorPathComponent_apply]
  -- Reorder the finite sums so the coordinate indices sit outside the partition sum.
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [Finset.sum_comm]

/-- Helper for Theorem 25.30: self quadratic covariation is exactly square variation. -/
theorem hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self
    {Y : PathSpace} {covYY : PathwiseProcess}
    (hYY : HasQuadraticCovariationAlong Y Y covYY) :
    HasSquareVariationAlong Y covYY := by
  intro T
  -- Proof comment: on the diagonal, the mixed dyadic sum is exactly the square-variation sum.
  convert HasQuadraticCovariationAlong.tendsto_partition_sum hYY T using 1
  ext n
  rw [dyadic_quadratic_covariation_sum, partitionQuadraticCovariationSum, partitionPVariationSum]
  refine Finset.sum_congr rfl ?_
  intro k hk
  simp [sq_abs]
  ring

/-- Helper for Theorem 25.30: the weighted mixed dyadic sums are the polarization of the weighted
square-variation sums of `Y + Z` and `Y - Z`. -/
theorem dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization
    (H : NNReal → ℝ) (Y Z : PathSpace) (T : NNReal) (n : ℕ) :
    dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n =
      (1 / 4 : ℝ) *
        (pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            H
            (Y + Z)
            dyadicPartitionSequence
            T
            n -
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            H
            (Y - Z)
            dyadicPartitionSequence
            T
            n) := by
  let s := Finset.range (partitionBoundIndex dyadicPartitionSequence n T)
  let addTerm : ℕ → ℝ := fun k ↦
    H (dyadicPartitionSequence n k) *
      (((Y + Z) (partitionNextPointUpTo dyadicPartitionSequence n k T) -
          (Y + Z) (dyadicPartitionSequence n k)) ^ 2)
  let subTerm : ℕ → ℝ := fun k ↦
    H (dyadicPartitionSequence n k) *
      (((Y - Z) (partitionNextPointUpTo dyadicPartitionSequence n k T) -
          (Y - Z) (dyadicPartitionSequence n k)) ^ 2)
  have hterm :
      ∀ k ∈ s,
        H (dyadicPartitionSequence n k) *
            (Y (partitionNextPointUpTo dyadicPartitionSequence n k T) -
              Y (dyadicPartitionSequence n k)) *
            (Z (partitionNextPointUpTo dyadicPartitionSequence n k T) -
              Z (dyadicPartitionSequence n k)) =
          (addTerm k - subTerm k) / 4 := by
    intro k hk
    simp only [addTerm, subTerm, ContinuousMap.add_apply, ContinuousMap.sub_apply]
    ring
  calc
    dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n
        = Finset.sum s (fun k ↦ (addTerm k - subTerm k) / 4) := by
            rw [dyadicQuadraticCovariationIntegralApproximationUpTo_def]
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k (by simpa [s] using hk)
    _ = (Finset.sum s addTerm - Finset.sum s subTerm) / 4 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ =
        (pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            H
            (Y + Z)
            dyadicPartitionSequence
            T
            n -
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            H
            (Y - Z)
            dyadicPartitionSequence
            T
            n) / 4 := by
      have haddSum :
          Finset.sum s addTerm =
            pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              H
              (Y + Z)
              dyadicPartitionSequence
              T
              n := by
        rfl
      have hsubSum :
          Finset.sum s subTerm =
            pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              H
              (Y - Z)
              dyadicPartitionSequence
              T
              n := by
        rfl
      rw [haddSum, hsubSum]
    _ =
        (1 / 4 : ℝ) *
          (pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              H
              (Y + Z)
              dyadicPartitionSequence
              T
              n -
            pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              H
              (Y - Z)
              dyadicPartitionSequence
              T
              n) := by
      ring

/-- Helper for Theorem 25.30: once each pairwise weighted dyadic covariation approximation has a
genuine limit, the multidimensional correction limit follows by finite-sum convergence. -/
theorem pathwiseMultidimensionalItoCorrection_spec_of_pairwise
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal)
    (hpair :
      ∀ i j : Fin d,
        Tendsto
          (fun n ↦
            dyadicQuadraticCovariationIntegralApproximationUpTo
              (fun s ↦ (∂²[i, j] F) (X s))
              (vectorPathComponent X i)
              (vectorPathComponent X j)
              T
              n)
          atTop
          (nhds
            (pathwiseQuadraticCovariationIntegral
              (fun s ↦ (∂²[i, j] F) (X s))
              (vectorPathComponent X i)
              (vectorPathComponent X j)
              T))) :
    Tendsto
      (fun n ↦ dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
      atTop
      (nhds (pathwiseMultidimensionalItoCorrection F X T)) := by
  have hsum :
      Tendsto
        (fun n ↦
          (1 / 2 : ℝ) *
            ∑ i : Fin d, ∑ j : Fin d,
              dyadicQuadraticCovariationIntegralApproximationUpTo
                (fun s ↦ (∂²[i, j] F) (X s))
                (vectorPathComponent X i)
                (vectorPathComponent X j)
                T
                n)
        atTop
        (nhds
          ((1 / 2 : ℝ) *
            ∑ i : Fin d, ∑ j : Fin d,
              pathwiseQuadraticCovariationIntegral
                (fun s ↦ (∂²[i, j] F) (X s))
                (vectorPathComponent X i)
                (vectorPathComponent X j)
                T)) := by
    -- Push the pairwise convergence theorem through the finite coordinate sums and scalar factor.
    refine tendsto_const_nhds.mul ?_
    refine tendsto_finset_sum _ fun i _ ↦ ?_
    exact tendsto_finset_sum _ fun j _ ↦ hpair i j
  simpa [dyadicMultidimensionalItoCorrectionApproximationUpTo_eq_sum_covariationApproximations,
    pathwiseMultidimensionalItoCorrection_def] using hsum

/-- Helper for Theorem 25.30: continuous weights turn the dyadic mixed-increment sums of `Y` and
`Z` into a genuine limit once continuous self- and mixed-covariation witnesses are available. -/
theorem tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_of_hasQuadraticCovariation
    (H : NNReal → ℝ) (hH : Continuous H)
    {Y Z covYY covZZ covYZ : PathSpace}
    (hYY : HasQuadraticCovariationAlong Y Y covYY)
    (hZZ : HasQuadraticCovariationAlong Z Z covZZ)
    (hYZ : HasQuadraticCovariationAlong Y Z covYZ)
    (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
      atTop
      (nhds (pathwiseQuadraticCovariationIntegral H Y Z T)) := by
  let covAdd : PathSpace := covYY + (2 : ℝ) • covYZ + covZZ
  let covSub : PathSpace := covYY - (2 : ℝ) • covYZ + covZZ
  have hSqYY : HasSquareVariationAlong Y covYY :=
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self hYY
  have hSqZZ : HasSquareVariationAlong Z covZZ :=
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self hZZ
  have hAdd : HasSquareVariationAlong (Y + Z) covAdd := by
    -- Proof comment: the plus path inherits the canonical polarized square-variation witness.
    simpa [covAdd] using
      hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong hSqYY hSqZZ hYZ
  have hSub : HasSquareVariationAlong (Y - Z) covSub := by
    -- Proof comment: the minus path is handled by the corresponding subtraction witness.
    simpa [covSub] using
      hasSquareVariationAlong_sub_of_hasQuadraticCovariationAlong hSqYY hSqZZ hYZ
  let L : ℝ :=
    (1 / 4 : ℝ) *
      ((∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hAdd)) -
        ∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hSub))
  have hAddLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y + Z) T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hAdd))) :=
    tendsto_weightedDyadicSquareVariationSum_of_continuous H hH hAdd T
  have hSubLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y - Z) T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, H s ∂(squareVariationStieltjesMeasure hSub))) :=
    tendsto_weightedDyadicSquareVariationSum_of_continuous H hH hSub T
  have hlim :
      Tendsto
        (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
        atTop
        (nhds L) := by
    have hpol :
        Tendsto
          (fun n ↦
            (1 / 4 : ℝ) *
              (weightedDyadicSquareVariationSum H (Y + Z) T n -
                weightedDyadicSquareVariationSum H (Y - Z) T n))
          atTop
          (nhds L) := by
      -- Proof comment: the plus/minus weighted square-variation limits assemble into the
      -- polarized mixed-increment limit.
      simpa [L] using (hAddLim.sub hSubLim).const_mul (1 / 4 : ℝ)
    refine hpol.congr' ?_
    filter_upwards with n
    -- Proof comment: each dyadic mixed sum is the quarter difference of the plus/minus weighted
    -- square-variation sums.
    simpa [weightedDyadicSquareVariationSum,
      pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def] using
      (dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization
        H Y Z T n).symm
  have hcanon :
      pathwiseQuadraticCovariationIntegral H Y Z T = L :=
    pathwiseQuadraticCovariationIntegral_eq_of_tendsto H Y Z T hlim
  simpa [hcanon] using hlim

/-- If `F ∈ C²(ℝ^d)` and `X ∈ 𝒞_qv^d`, then the dyadic second-order correction sums converge to
the source-facing quadratic-covariation correction term
`pathwiseMultidimensionalItoCorrection F X T`. -/
theorem pathwiseMultidimensionalItoCorrection_spec
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (hX : X ∈ (𝒞_qv^d)) (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
      atTop
      (nhds (pathwiseMultidimensionalItoCorrection F X T)) := by
  -- Route correction: instead of rebuilding a mixed signed-measure theorem first, reduce the
  -- finite correction sum to the local pairwise convergence theorem above.
  rcases (mem_𝒞_qv_d_iff_exists_family X).mp hX with ⟨cov, hcov⟩
  refine pathwiseMultidimensionalItoCorrection_spec_of_pairwise F X T ?_
  intro i j
  -- Each Hessian-entry weight is continuous because `F` is `C²` and `X` is continuous.
  have hWeight : Continuous fun s : NNReal ↦ (∂²[i, j] F) (X s) :=
    (continuous_secondPartialDeriv F hf i j).comp X.continuous
  -- Apply the pairwise dyadic convergence theorem to the chosen coordinate covariation owners.
  simpa using
    tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_of_hasQuadraticCovariation
      (fun s ↦ (∂²[i, j] F) (X s))
      hWeight
      (hcov i i)
      (hcov j j)
      (hcov i j)
      T

/-- Helper for Theorem 25.30: the rowwise multidimensional Taylor remainder after subtracting the
left-point gradient term and the left-point quadratic correction term. -/
noncomputable def partitionPathwiseMultidimensionalItoTaylorRemainder
    (F : State → ℝ) (X : VectorPathSpace d) (T : NNReal) (n : ℕ) : ℝ :=
  F (X T) - F (X 0) -
    dyadicMultidimensionalItoApproximationUpTo F X T n -
    dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n

/-- Helper for Theorem 25.30: summing the one-step Taylor expansions of `F` along the dyadic row
recovers the endpoint increment `F (X T) - F (X 0)`. -/
theorem dyadicMultidimensionalItoTaylorDecomposition_eq
    (F : State → ℝ) (_hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    F (X T) - F (X 0) =
      dyadicMultidimensionalItoApproximationUpTo F X T n +
        dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n +
        partitionPathwiseMultidimensionalItoTaylorRemainder F X T n := by
  -- Route correction: after redefining the remainder as the algebraic residual, the decomposition
  -- is the tautological identity obtained by adding the residual back.
  rw [partitionPathwiseMultidimensionalItoTaylorRemainder]
  ring

/-- Helper for Theorem 25.30: every Hessian entry has small oscillation on all dyadic line
segments once the dyadic mesh is sufficiently fine. -/
theorem eventually_secondPartialOscillation_on_dyadicSegments
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (T : NNReal) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      ∀ i j : Fin d,
        ∀ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
          ∀ u ∈ Set.uIcc (0 : ℝ) 1,
            ∀ v ∈ Set.uIcc (0 : ℝ) 1,
              |(∂²[i, j] F)
                    (X (dyadicPartitionSequence n k) +
                      u • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                        X (dyadicPartitionSequence n k))) -
                  (∂²[i, j] F)
                    (X (dyadicPartitionSequence n k) +
                      v • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                        X (dyadicPartitionSequence n k)))| ≤
                2 * ε := by
  classical
  have hpair :
      ∀ i j : Fin d,
        ∀ᶠ n in atTop,
          ∀ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
            ∀ u ∈ Set.uIcc (0 : ℝ) 1,
              ∀ v ∈ Set.uIcc (0 : ℝ) 1,
                |(∂²[i, j] F)
                      (X (dyadicPartitionSequence n k) +
                        u • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                          X (dyadicPartitionSequence n k))) -
                    (∂²[i, j] F)
                      (X (dyadicPartitionSequence n k) +
                        v • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                          X (dyadicPartitionSequence n k)))| ≤
                  2 * ε := by
    intro i j
    obtain ⟨C, hC⟩ :
        ∃ C : ℝ, ∀ t ∈ Set.Icc (0 : NNReal) T, ‖X t‖ ≤ C :=
      (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
        X.continuous.continuousOn
    have hC_nonneg : 0 ≤ C := by
      have h0norm : 0 ≤ ‖X 0‖ := norm_nonneg (X 0)
      exact le_trans h0norm (hC 0 (by simp))
    have hSecondUC :
        UniformContinuousOn (∂²[i, j] F) (Metric.closedBall (0 : State) C) := by
      -- Proof comment: the Hessian entry is uniformly continuous on the compact ball that
      -- contains every dyadic line segment of the path.
      exact
        (ProperSpace.isCompact_closedBall (0 : State) C).uniformContinuousOn_of_continuous
          ((continuous_secondPartialDeriv F hf i j).continuousOn)
    have hXPathUC : UniformContinuousOn X (Set.Icc (0 : NNReal) T) := by
      -- Proof comment: the path itself is uniformly continuous on the compact time interval.
      exact isCompact_Icc.uniformContinuousOn_of_continuous X.continuous.continuousOn
    rcases (Metric.uniformContinuousOn_iff_le.mp hSecondUC) (2 * ε) (by linarith) with
      ⟨δ, hδ_pos, hδ_spec⟩
    rcases (Metric.uniformContinuousOn_iff_le.mp hXPathUC) δ hδ_pos with
      ⟨η, hη_pos, hη_spec⟩
    have hmesh :
        ∀ᶠ n in atTop, partitionMesh dyadicPartitionSequence n ≤ ENNReal.ofReal η := by
      -- Proof comment: eventual mesh control converts the time modulus into a spatial modulus
      -- for each dyadic interval.
      exact
        (ENNReal.tendsto_nhds_zero.1
          (IsAdmissiblePartitionSequence.mesh_tendsto_zero (P := dyadicPartitionSequence)))
          (ENNReal.ofReal η) (ENNReal.ofReal_pos.2 hη_pos)
    filter_upwards [hmesh] with n hn k hk u hu v hv
    have hk_lt : k < partitionBoundIndex dyadicPartitionSequence n T := Finset.mem_range.mp hk
    have hleftTime :
        dyadicPartitionSequence n k ∈ Set.Icc (0 : NNReal) T :=
      partitionPoint_mem_Icc_of_lt_truncationBoundIndex dyadicPartitionSequence n k T hk_lt
    have hrightTime :
        partitionNextPointUpTo dyadicPartitionSequence n k T ∈ Set.Icc (0 : NNReal) T :=
      partitionNextPointUpTo_mem_Icc_of_lt_partitionBoundIndex
        dyadicPartitionSequence n k T hk_lt
    have huIcc : u ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hu
    have hvIcc : v ∈ Set.Icc (0 : ℝ) 1 := by
      simpa [Set.uIcc_of_le (show (0 : ℝ) ≤ 1 by norm_num)] using hv
    let x : State := X (dyadicPartitionSequence n k)
    let y : State := X (partitionNextPointUpTo dyadicPartitionSequence n k T)
    have hx_norm : ‖x‖ ≤ C := by
      exact hC _ hleftTime
    have hy_norm : ‖y‖ ≤ C := by
      exact hC _ hrightTime
    have htime :
        dist (dyadicPartitionSequence n k) (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
          η := by
      have hedist :
          edist
              (dyadicPartitionSequence n k)
              (partitionNextPointUpTo dyadicPartitionSequence n k T) ≤
            ENNReal.ofReal η := by
        exact
          (edist_partitionPoint_partitionNextPointUpTo_le_truncationMesh
            dyadicPartitionSequence n k T hk_lt).trans hn
      exact (edist_le_ofReal (le_of_lt hη_pos)).1 hedist
    have hendpoint : dist x y ≤ δ := by
      -- Proof comment: small mesh makes the dyadic endpoint values close in the state space.
      exact hη_spec _ hleftTime _ hrightTime htime
    have hsegment_mem :
        ∀ w ∈ Set.Icc (0 : ℝ) 1, x + w • (y - x) ∈ Metric.closedBall (0 : State) C := by
      intro w hw
      have hw0 : 0 ≤ w := hw.1
      have hw1 : w ≤ 1 := hw.2
      have hrewrite : x + w • (y - x) = (1 - w) • x + w • y := by
        ext m
        simp [x, y]
        ring
      have hnorm :
          ‖x + w • (y - x)‖ ≤ C := by
        calc
          ‖x + w • (y - x)‖ = ‖(1 - w) • x + w • y‖ := by
            rw [hrewrite]
          _ ≤ ‖(1 - w) • x‖ + ‖w • y‖ := norm_add_le _ _
          _ = |1 - w| * ‖x‖ + |w| * ‖y‖ := by
            rw [norm_smul, norm_smul]
            simp only [Real.norm_eq_abs]
          _ ≤ (1 - w) * C + w * C := by
            have hw1' : 0 ≤ 1 - w := sub_nonneg.mpr hw1
            rw [abs_of_nonneg hw1', abs_of_nonneg hw0]
            gcongr
          _ = C := by
            ring
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm
    have huv : |u - v| ≤ 1 := by
      refine abs_le.mpr ?_
      constructor
      · linarith [huIcc.1, hvIcc.2]
      · linarith [huIcc.2, hvIcc.1]
    have hdist :
        dist (x + u • (y - x)) (x + v • (y - x)) ≤ δ := by
      calc
        dist (x + u • (y - x)) (x + v • (y - x))
            = ‖(u - v) • (y - x)‖ := by
                rw [dist_eq_norm]
                congr 1
                ext m
                simp [x, y]
                ring
        _ = |u - v| * ‖y - x‖ := by
              rw [norm_smul]
              simp only [Real.norm_eq_abs]
        _ ≤ 1 * ‖y - x‖ := by
              gcongr
        _ = dist x y := by
              rw [dist_eq_norm, norm_sub_rev]
              simp
        _ ≤ δ := hendpoint
    -- Proof comment: both segment points stay in the compact ball, and their distance is
    -- controlled by the endpoint distance of the dyadic interval.
    simpa [x, y, Real.dist_eq] using
      hδ_spec
        (x + u • (y - x))
        (hsegment_mem _ huIcc)
        (x + v • (y - x))
        (hsegment_mem _ hvIcc)
        hdist
  choose N hN using fun ij : Fin d × Fin d ↦ Filter.eventually_atTop.1 (hpair ij.1 ij.2)
  let Nmax : ℕ := Finset.univ.sup N
  -- Proof comment: finitely many coordinate pairs are involved, so one common row index works
  -- for all Hessian entries simultaneously.
  refine Filter.eventually_atTop.2 ⟨Nmax, ?_⟩
  intro n hn i j
  exact hN (i, j) n (le_trans (Finset.le_sup (Finset.mem_univ (i, j))) hn)

/-- Helper for Theorem 25.30: a uniformly bounded coefficient matrix contributes at most `d`
times the diagonal square mass when paired with one increment vector. -/
private theorem abs_sum_mul_mul_le_card_mul_sum_sq
    {ε : ℝ} (hε : 0 ≤ ε)
    (A : Fin d → Fin d → ℝ) (δ : Fin d → ℝ)
    (hA : ∀ i j : Fin d, |A i j| ≤ ε) :
    |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| ≤
      ε * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
  have habs :
      |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| ≤
        ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := by
    calc
      |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j|
          ≤ ∑ i : Fin d, |∑ j : Fin d, A i j * δ i * δ j| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun i : Fin d ↦ ∑ j : Fin d, A i j * δ i * δ j)
                (Finset.univ : Finset (Fin d)))
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := by
            refine Finset.sum_le_sum ?_
            intro i hi
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun j : Fin d ↦ A i j * δ i * δ j)
                (Finset.univ : Finset (Fin d)))
  have hcoeff :
      ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| ≤
        ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j| := by
    refine Finset.sum_le_sum ?_
    intro i hi
    refine Finset.sum_le_sum ?_
    intro j hj
    have hδ_nonneg : 0 ≤ |δ i| * |δ j| := by positivity
    have hmul :
        |A i j| * (|δ i| * |δ j|) ≤ ε * (|δ i| * |δ j|) :=
      mul_le_mul_of_nonneg_right (hA i j) hδ_nonneg
    simpa [abs_mul, mul_assoc, mul_left_comm, mul_comm] using hmul
  have hsum_sq :
      (∑ i : Fin d, |δ i|) ^ 2 ≤ (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
    simpa [sq_abs] using
      (sq_sum_le_card_mul_sum_sq
        (s := (Finset.univ : Finset (Fin d)))
        (f := fun i : Fin d ↦ |δ i|))
  have hεsum_sq :
      ε * (∑ i : Fin d, |δ i|) ^ 2 ≤ ε * ((d : ℝ) * ∑ i : Fin d, (δ i)^2) :=
    mul_le_mul_of_nonneg_left hsum_sq hε
  calc
    |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j|
        ≤ ∑ i : Fin d, ∑ j : Fin d, |A i j * δ i * δ j| := habs
    _ ≤ ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j| := hcoeff
    _ = ε * (∑ i : Fin d, |δ i|) ^ 2 := by
      calc
        ∑ i : Fin d, ∑ j : Fin d, ε * |δ i| * |δ j|
            = ∑ i : Fin d, (ε * |δ i|) * ∑ j : Fin d, |δ j| := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                rw [Finset.mul_sum]
        _ = (∑ i : Fin d, ε * |δ i|) * ∑ j : Fin d, |δ j| := by
              rw [← Finset.sum_mul]
        _ = ε * (∑ i : Fin d, |δ i|) * ∑ j : Fin d, |δ j| := by
              rw [← Finset.mul_sum]
        _ = ε * (∑ i : Fin d, |δ i|) ^ 2 := by
              ring
    _ ≤ ε * ((d : ℝ) * ∑ i : Fin d, (δ i)^2) := hεsum_sq
    _ = ε * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by ring

/-- Helper for Theorem 25.30: summing the clipped increments of a continuous path along one
partition row telescopes to the endpoint increment on `[0,T]`. -/
theorem partitionIncrementSum_eq_endpointIncrement
    (G : C(NNReal, ℝ)) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (T : NNReal) (n : ℕ) :
    Finset.sum (Finset.range (partitionBoundIndex P n T)) (fun k ↦
        G (partitionNextPointUpTo P n k T) - G (P n k)) =
      G T - G 0 := by
  let m := partitionBoundIndex P n T
  -- Proof comment: split off the final clipped increment; before that index the row telescopes,
  -- and the final clipped successor is exactly `T`.
  by_cases hm : m = 0
  · have hT0 : T = 0 := by
      have hle : T ≤ P n 0 := by
        simpa [m, hm] using le_partitionBoundIndex_time P n T
      simpa [IsAdmissiblePartitionSequence.zero_eq (P := P) n] using hle
    have hm0 : partitionBoundIndex P n T = 0 := by
      simpa [m] using hm
    rw [hm0, Finset.sum_range_zero, hT0]
    ring
  · obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hm
    have hkm : partitionBoundIndex P n T = k.succ := by
      simpa [m] using hk
    have hsum :
        ∀ r : ℕ,
          Finset.sum (Finset.range r) (fun j ↦ G (P n (j + 1)) - G (P n j)) =
            G (P n r) - G (P n 0) := by
      intro r
      induction r with
      | zero =>
          simp
      | succ r ihr =>
          rw [Finset.sum_range_succ, ihr]
          abel
    rw [hkm, Finset.sum_range_succ]
    have hprefix :
        Finset.sum (Finset.range k) (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
          G (P n k) - G (P n 0) := by
      -- Before the final contributing index, truncation is inactive.
      have hraw :
          Finset.sum (Finset.range k) (fun j ↦ G (partitionNextPointUpTo P n j T) - G (P n j)) =
            Finset.sum (Finset.range k) (fun j ↦ G (P n (j + 1)) - G (P n j)) := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        have hj_lt : j + 1 < partitionBoundIndex P n T := by
          simpa [m, hk] using Nat.succ_lt_succ (Finset.mem_range.mp hj)
        have hnext : partitionNextPointUpTo P n j T = P n (j + 1) := by
          rw [partitionNextPointUpTo, min_eq_left]
          exact le_of_lt (partitionPoint_lt_time_of_lt_truncationBoundIndex P n (j + 1) T hj_lt)
        rw [hnext]
      exact hraw.trans (hsum k)
    have hlast : G (partitionNextPointUpTo P n k T) - G (P n k) = G T - G (P n k) := by
      -- The last clipped successor is exactly `T`.
      have hnext : partitionNextPointUpTo P n k T = T := by
        rw [partitionNextPointUpTo, min_eq_right]
        simpa [m, hk] using le_partitionBoundIndex_time P n T
      rw [hnext]
    rw [hprefix, hlast]
    simp [IsAdmissiblePartitionSequence.zero_eq (P := P) n]

/-- Helper for Theorem 25.30: the scalar left-point Taylor remainder is controlled by the
oscillation of the second derivative on the segment between the endpoints. -/
lemma leftpointTaylorIncrementError_le
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    {a b ε : ℝ} (hab : a ≤ b) (hε : 0 ≤ ε)
    (hosc :
      ∀ x ∈ Set.uIcc a b, ∀ y ∈ Set.uIcc a b,
        |iteratedDeriv 2 F x - iteratedDeriv 2 F y| ≤ ε) :
    |F b - F a - deriv F a * (b - a) -
        ((1 : ℝ) / 2) * iteratedDeriv 2 F a * (b - a) ^ 2| ≤
      ε * (b - a) ^ 2 := by
  by_cases hlt : a < b
  · obtain ⟨ξ, hξ, hTaylor⟩ :=
      taylor_mean_remainder_lagrange_iteratedDeriv
        (f := F) (x₀ := a) (x := b) (n := 1) hlt hF.contDiffOn
    have hTaylor' :
        F b - F a - deriv F a * (b - a) =
          iteratedDeriv 2 F ξ * (b - a) ^ 2 / 2 := by
      -- Proof comment: rewrite the first-order Taylor polynomial at `a` through the ordinary
      -- derivative of `F`.
      have hTaylorEval :
          taylorWithinEval F 1 (Set.Icc a b) a b = F a + deriv F a * (b - a) := by
        rw [taylorWithinEval_succ, taylor_within_zero_eval]
        have hderivWithin :
            derivWithin F (Set.Icc a b) a = deriv F a := by
          exact
            (hF.differentiable (by norm_num) a).derivWithin
              ((uniqueDiffOn_Icc hlt).uniqueDiffWithinAt ⟨le_rfl, hab⟩)
        rw [iteratedDerivWithin_one, hderivWithin, smul_eq_mul]
        ring_nf
      rw [hTaylorEval] at hTaylor
      linarith
    have hξ_mem : ξ ∈ Set.uIcc a b := by
      simpa [Set.uIcc_of_le hab] using (show ξ ∈ Set.Icc a b from ⟨hξ.1.le, hξ.2.le⟩)
    have ha_mem : a ∈ Set.uIcc a b := by
      simpa [Set.uIcc_of_le hab] using (show a ∈ Set.Icc a b from ⟨le_rfl, hab⟩)
    have hmain :
        F b - F a - deriv F a * (b - a) -
            ((1 : ℝ) / 2) * iteratedDeriv 2 F a * (b - a) ^ 2 =
          (iteratedDeriv 2 F ξ - iteratedDeriv 2 F a) * (b - a) ^ 2 / 2 := by
      linarith
    calc
      |F b - F a - deriv F a * (b - a) -
          ((1 : ℝ) / 2) * iteratedDeriv 2 F a * (b - a) ^ 2|
          = |(iteratedDeriv 2 F ξ - iteratedDeriv 2 F a) * (b - a) ^ 2 / 2| := by
              rw [hmain]
      _ = |iteratedDeriv 2 F ξ - iteratedDeriv 2 F a| * (b - a) ^ 2 / 2 := by
            rw [div_eq_mul_inv, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (b - a))]
            ring_nf
      _ ≤ ε * (b - a) ^ 2 := by
            have hbound : |iteratedDeriv 2 F ξ - iteratedDeriv 2 F a| ≤ ε :=
              hosc ξ hξ_mem a ha_mem
            have hsq_nonneg : 0 ≤ (b - a) ^ 2 := sq_nonneg (b - a)
            nlinarith
  · have hab_eq : a = b := le_antisymm hab (not_lt.mp hlt)
    subst hab_eq
    simp

/-- Helper for Theorem 25.30: the algebraic remainder is the sum of the cellwise Taylor errors
along the clipped dyadic row. -/
private theorem partitionPathwiseMultidimensionalItoTaylorRemainder_eq_sum_cellwiseError
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (T : NNReal) (n : ℕ) :
    partitionPathwiseMultidimensionalItoTaylorRemainder F X T n =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
        F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
          F (X (dyadicPartitionSequence n k)) -
          (∑ i : Fin d,
            (∂[i] F) (X (dyadicPartitionSequence n k)) *
              (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
                X (dyadicPartitionSequence n k) i)) -
          (1 / 2 : ℝ) *
            ∑ i : Fin d, ∑ j : Fin d,
              (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
                  X (dyadicPartitionSequence n k) i) *
                (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
                  X (dyadicPartitionSequence n k) j) := by
  let FX : C(NNReal, ℝ) :=
    ⟨fun t ↦ F (X t), hf.continuous.comp X.continuous⟩
  have htel :
      F (X T) - F (X 0) =
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T)) fun k ↦
          F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
            F (X (dyadicPartitionSequence n k)) := by
    simpa [FX] using
      (partitionIncrementSum_eq_endpointIncrement FX dyadicPartitionSequence T n).symm
  -- Proof comment: rewrite the endpoint increment as the telescoping sum of cell increments and
  -- subtract the first- and second-order dyadic sums termwise.
  rw [partitionPathwiseMultidimensionalItoTaylorRemainder,
    dyadicMultidimensionalItoApproximationUpTo_def,
    dyadicMultidimensionalItoCorrectionApproximationUpTo_def,
    htel, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]

/-- Helper for Theorem 25.30: one dyadic cell is controlled by the scalar left-point Taylor
estimate applied to the line `u ↦ F (x + u • δ)`. -/
private theorem abs_cellwiseLineTaylorError_le
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (T : NNReal) (n k : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (_hk : k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T))
    (hosc :
      ∀ i j : Fin d,
        ∀ u ∈ Set.uIcc (0 : ℝ) 1,
          ∀ v ∈ Set.uIcc (0 : ℝ) 1,
            |(∂²[i, j] F)
                  (X (dyadicPartitionSequence n k) +
                    u • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                      X (dyadicPartitionSequence n k))) -
                (∂²[i, j] F)
                  (X (dyadicPartitionSequence n k) +
                    v • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                      X (dyadicPartitionSequence n k)))| ≤
              2 * ε) :
    |F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
        F (X (dyadicPartitionSequence n k)) -
        (∑ i : Fin d,
          (∂[i] F) (X (dyadicPartitionSequence n k)) *
            (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
              X (dyadicPartitionSequence n k) i)) -
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
            (∂²[i, j] F) (X (dyadicPartitionSequence n k)) *
              (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
                X (dyadicPartitionSequence n k) i) *
              (X (partitionNextPointUpTo dyadicPartitionSequence n k T) j -
                X (dyadicPartitionSequence n k) j)| ≤
      (2 * ε) * (d : ℝ) *
        ∑ i : Fin d,
          (X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
            X (dyadicPartitionSequence n k) i) ^ 2 := by
  let x : State := X (dyadicPartitionSequence n k)
  let y : State := X (partitionNextPointUpTo dyadicPartitionSequence n k T)
  let δ : State := y - x
  let g : ℝ → ℝ := fun u ↦ F (x + u • δ)
  let η : ℝ := (2 * ε) * (d : ℝ) * ∑ i : Fin d, (δ i)^2
  have hg : ContDiff ℝ 2 g := by
    -- Proof comment: restricting a `C²` map to an affine line preserves `C²` regularity.
    fun_prop
  have hsum_nonneg : 0 ≤ ∑ i : Fin d, (δ i)^2 := by
    exact Finset.sum_nonneg fun i hi ↦ sq_nonneg (δ i)
  have hη_nonneg : 0 ≤ η := by
    positivity
  have hlineOsc :
      ∀ u ∈ Set.uIcc (0 : ℝ) 1, ∀ v ∈ Set.uIcc (0 : ℝ) 1,
        |iteratedDeriv 2 g u - iteratedDeriv 2 g v| ≤ η := by
    intro u hu v hv
    let A : Fin d → Fin d → ℝ := fun i j ↦
      (∂²[i, j] F) (x + u • δ) - (∂²[i, j] F) (x + v • δ)
    have hA : ∀ i j : Fin d, |A i j| ≤ 2 * ε := by
      intro i j
      simpa [A, x, δ] using hosc i j u hu v hv
    calc
      |iteratedDeriv 2 g u - iteratedDeriv 2 g v|
          = |∑ i : Fin d, ∑ j : Fin d, A i j * δ i * δ j| := by
              rw [lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul F hf x δ u,
                lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul F hf x δ v]
              congr 1
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro i hi
              rw [← Finset.sum_sub_distrib]
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [A]
              ring
      _ ≤ (2 * ε) * (d : ℝ) * ∑ i : Fin d, (δ i)^2 := by
            exact
              abs_sum_mul_mul_le_card_mul_sum_sq
                (d := d) (ε := 2 * ε) (show 0 ≤ 2 * ε by nlinarith) A δ hA
      _ = η := by rfl
  have hTaylor :
      |g 1 - g 0 - deriv g 0 * (1 - 0) -
          ((1 : ℝ) / 2) * iteratedDeriv 2 g 0 * (1 - 0) ^ 2| ≤
        η * (1 - 0) ^ 2 := by
    exact leftpointTaylorIncrementError_le g hg (a := 0) (b := 1) (ε := η) (by norm_num)
      hη_nonneg hlineOsc
  have hderiv0 :
      deriv g 0 = ∑ i : Fin d, (∂[i] F) x * δ i := by
    simpa [g] using
      lineDeriv_eq_sum_partialDeriv_mul F (hf.differentiable (by norm_num)) x δ 0
  have hsecond0 :
      iteratedDeriv 2 g 0 = ∑ i : Fin d, ∑ j : Fin d, (∂²[i, j] F) x * δ i * δ j := by
    simpa [g] using lineSecondDeriv_eq_sum_secondPartialDeriv_mul_mul F hf x δ 0
  have hzero : x + (0 : ℝ) • δ = x := by simp
  have hone : x + (1 : ℝ) • δ = y := by
    ext i
    simp [δ, x, y]
  -- Proof comment: rewrite the scalar line estimate back into the endpoint, gradient, and Hessian
  -- data of the current dyadic cell.
  rw [hderiv0, hsecond0] at hTaylor
  simpa [g, x, y, δ, η, hzero, hone] using hTaylor

/-- Helper for Theorem 25.30: if every Hessian entry has small oscillation on every contributing
dyadic line segment, then the full rowwise Taylor remainder is controlled by the coordinate square
masses. -/
theorem abs_partitionPathwiseMultidimensionalItoTaylorRemainder_le
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d) (T : NNReal) (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε)
    (hosc :
      ∀ i j : Fin d,
        ∀ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
          ∀ u ∈ Set.uIcc (0 : ℝ) 1,
            ∀ v ∈ Set.uIcc (0 : ℝ) 1,
              |(∂²[i, j] F)
                    (X (dyadicPartitionSequence n k) +
                      u • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                        X (dyadicPartitionSequence n k))) -
                  (∂²[i, j] F)
                    (X (dyadicPartitionSequence n k) +
                      v • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                        X (dyadicPartitionSequence n k)))| ≤
                2 * ε) :
    |partitionPathwiseMultidimensionalItoTaylorRemainder F X T n| ≤
      (2 * ε) * (d : ℝ) *
        ∑ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (vectorPathComponent X i)
            dyadicPartitionSequence
            T
            n := by
  let N := partitionBoundIndex dyadicPartitionSequence n T
  let inc : ℕ → Fin d → ℝ := fun k i ↦
    X (partitionNextPointUpTo dyadicPartitionSequence n k T) i -
      X (dyadicPartitionSequence n k) i
  -- Proof comment: bound the absolute value of the rowwise error by the sum of the cellwise
  -- errors and then commute the cell and coordinate sums to recover the diagonal quadratic masses.
  calc
    |partitionPathwiseMultidimensionalItoTaylorRemainder F X T n|
        = |Finset.sum (Finset.range N) (fun k ↦
            F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
              F (X (dyadicPartitionSequence n k)) -
              (∑ i : Fin d,
                (∂[i] F) (X (dyadicPartitionSequence n k)) * inc k i) -
              (1 / 2 : ℝ) *
                ∑ i : Fin d, ∑ j : Fin d,
                  (∂²[i, j] F) (X (dyadicPartitionSequence n k)) * inc k i * inc k j)| := by
            simpa [N, inc] using
              congrArg abs
                (partitionPathwiseMultidimensionalItoTaylorRemainder_eq_sum_cellwiseError
                  F hf X T n)
    _ ≤ Finset.sum (Finset.range N) (fun k ↦
          |F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
              F (X (dyadicPartitionSequence n k)) -
              (∑ i : Fin d,
                (∂[i] F) (X (dyadicPartitionSequence n k)) * inc k i) -
              (1 / 2 : ℝ) *
                ∑ i : Fin d, ∑ j : Fin d,
                  (∂²[i, j] F) (X (dyadicPartitionSequence n k)) * inc k i * inc k j|) := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (fun k : ℕ ↦
                  F (X (partitionNextPointUpTo dyadicPartitionSequence n k T)) -
                    F (X (dyadicPartitionSequence n k)) -
                    (∑ i : Fin d,
                      (∂[i] F) (X (dyadicPartitionSequence n k)) * inc k i) -
                    (1 / 2 : ℝ) *
                      ∑ i : Fin d, ∑ j : Fin d,
                        (∂²[i, j] F) (X (dyadicPartitionSequence n k)) * inc k i * inc k j)
                (Finset.range N))
    _ ≤ Finset.sum (Finset.range N) (fun k ↦
          (2 * ε) * (d : ℝ) * ∑ i : Fin d, (inc k i)^2) := by
            refine Finset.sum_le_sum ?_
            intro k hk
            simpa [inc] using
              abs_cellwiseLineTaylorError_le F hf X T n k hε hk
                (fun i j u hu v hv ↦ hosc i j k (by simpa [N] using hk) u hu v hv)
    _ = (2 * ε) * (d : ℝ) * ∑ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (vectorPathComponent X i)
            dyadicPartitionSequence
            T
            n := by
            rw [← Finset.mul_sum, Finset.sum_comm]
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            rw [pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def]
            refine Finset.sum_congr rfl ?_
            intro k hk
            simp [inc, vectorPathComponent_apply]

/-- Helper for Theorem 25.30: the dyadic Taylor remainder at the fixed horizon `T` tends to `0`
once the one-step Taylor expansion is summed over the dyadic row and compared with the quadratic
correction sequence. -/
theorem tendsto_dyadicMultidimensionalItoTaylorRemainder
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d)) (T : NNReal) :
    Tendsto
      (fun n ↦
        F (X T) - F (X 0) -
          dyadicMultidimensionalItoApproximationUpTo F X T n -
          dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
      atTop
      (nhds 0) := by
  rcases (mem_𝒞_qv_d_iff_exists_family X).mp hX with ⟨cov, hcov⟩
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let M : ℝ := ∑ i : Fin d, (|cov i i T| + 1)
  let B : ℝ := (d : ℝ) * M + 1
  let η : ℝ := ε / (2 * B)
  have hM_nonneg : 0 ≤ M := by
    dsimp [M]
    refine Finset.sum_nonneg ?_
    intro i hi
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    nlinarith
  have hη_pos : 0 < η := by
    dsimp [η]
    exact div_pos hε (by positivity)
  have hη_nonneg : 0 ≤ η := hη_pos.le
  have hOsc :
      ∀ᶠ n in atTop,
        ∀ i j : Fin d,
          ∀ k ∈ Finset.range (partitionBoundIndex dyadicPartitionSequence n T),
            ∀ u ∈ Set.uIcc (0 : ℝ) 1,
              ∀ v ∈ Set.uIcc (0 : ℝ) 1,
                |(∂²[i, j] F)
                      (X (dyadicPartitionSequence n k) +
                        u • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                          X (dyadicPartitionSequence n k))) -
                    (∂²[i, j] F)
                      (X (dyadicPartitionSequence n k) +
                        v • (X (partitionNextPointUpTo dyadicPartitionSequence n k T) -
                          X (dyadicPartitionSequence n k)))| ≤
                  2 * η :=
    eventually_secondPartialOscillation_on_dyadicSegments F hf X T hη_pos
  have hmass_i :
      ∀ i : Fin d,
        ∀ᶠ n in atTop,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              (vectorPathComponent X i)
              dyadicPartitionSequence
              T
              n ≤
            |cov i i T| + 1 := by
    intro i
    have hsq : HasSquareVariationAlong (vectorPathComponent X i) (cov i i) :=
      hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self (hcov i i)
    simpa [pathwiseWeightedPartitionQuadraticVariationApproximationUpTo_def,
      weightedDyadicSquareVariationSum, vectorPathComponent_apply] using
      eventually_le_weightedDyadicSquareVariationSum_one_abs_add_one hsq T
  have hmassAll :
      ∀ᶠ n in atTop,
        ∀ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
              (fun _ ↦ (1 : ℝ))
              (vectorPathComponent X i)
              dyadicPartitionSequence
              T
              n ≤
            |cov i i T| + 1 := by
    choose N hN using fun i : Fin d ↦ Filter.eventually_atTop.1 (hmass_i i)
    let Nmax : ℕ := Finset.univ.sup N
    refine Filter.eventually_atTop.2 ⟨Nmax, ?_⟩
    intro n hn i
    exact hN i n (le_trans (Finset.le_sup (Finset.mem_univ i)) hn)
  have hmass :
      ∀ᶠ n in atTop,
        ∑ i : Fin d,
          pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
            (fun _ ↦ (1 : ℝ))
            (vectorPathComponent X i)
            dyadicPartitionSequence
            T
            n ≤
          M := by
    filter_upwards [hmassAll] with n hn
    dsimp [M]
    exact Finset.sum_le_sum fun i hi ↦ hn i
  have hdMB : (d : ℝ) * M < B := by
    dsimp [B]
    linarith
  have hstrict :
      (2 * η) * (d : ℝ) * M < ε := by
    have hratio : ((d : ℝ) * M) / B < 1 := by
      exact (div_lt_one hB_pos).2 hdMB
    have hmul : ε * (((d : ℝ) * M) / B) < ε := by
      simpa using mul_lt_mul_of_pos_left hratio hε
    simpa [η, B, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using hmul
  have hfactor_nonneg : 0 ≤ (2 * η) * (d : ℝ) := by positivity
  have hfinal :
      ∀ᶠ n in atTop,
        dist
          (F (X T) - F (X 0) -
            dyadicMultidimensionalItoApproximationUpTo F X T n -
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
          0 < ε := by
    filter_upwards [hOsc, hmass] with n hnOsc hnMass
    have hbound :=
      abs_partitionPathwiseMultidimensionalItoTaylorRemainder_le F hf X T n hη_nonneg hnOsc
    have hscaled :
        (2 * η) * (d : ℝ) *
            ∑ i : Fin d,
              pathwiseWeightedPartitionQuadraticVariationApproximationUpTo
                (fun _ ↦ (1 : ℝ))
                (vectorPathComponent X i)
                dyadicPartitionSequence
                T
                n ≤
          (2 * η) * (d : ℝ) * M :=
      mul_le_mul_of_nonneg_left hnMass hfactor_nonneg
    have hlt :
        |F (X T) - F (X 0) -
            dyadicMultidimensionalItoApproximationUpTo F X T n -
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n| < ε :=
      lt_of_le_of_lt hbound (lt_of_le_of_lt hscaled hstrict)
    simpa [Real.dist_eq] using hlt
  simpa using hfinal

-- Proof sketch: apply the scalar pathwise Itô formula to the one-dimensional paths obtained by
-- freezing all but one coordinate, sum the first-order terms over the coordinates, and identify
-- the second-order contributions with the pairwise signed covariation measures `d⟨Xⁱ,Xʲ⟩`.
/-- The dyadic left-point sums defining the multidimensional pathwise Itô integral converge on
`[0,T]` for any path in `𝒞_qv^d`. -/
theorem tendsto_dyadicMultidimensionalItoApproximationUpTo
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d)) (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n)
      atTop
      (nhds (pathwiseMultidimensionalItoIntegral F X T)) := by
  let L : ℝ := F (X T) - F (X 0) - pathwiseMultidimensionalItoCorrection F X T
  have hR :
      Tendsto
        (fun n ↦
          F (X T) - F (X 0) -
            dyadicMultidimensionalItoApproximationUpTo F X T n -
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
        atTop
        (nhds 0) :=
    tendsto_dyadicMultidimensionalItoTaylorRemainder F hf X hX T
  have hCorr :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
        atTop
        (nhds (pathwiseMultidimensionalItoCorrection F X T)) :=
    pathwiseMultidimensionalItoCorrection_spec F hf X hX T
  have hsum :
      Tendsto
        (fun n ↦
          (F (X T) - F (X 0) -
              dyadicMultidimensionalItoApproximationUpTo F X T n -
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
        atTop
        (nhds (pathwiseMultidimensionalItoCorrection F X T)) := by
    -- Proof comment: the Taylor remainder tends to `0`, so adding back the convergent correction
    -- leaves exactly the correction limit.
    simpa using hR.add hCorr
  have hlim :
      Tendsto
        (fun n ↦
          F (X T) - F (X 0) -
            ((F (X T) - F (X 0) -
                dyadicMultidimensionalItoApproximationUpTo F X T n -
                dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n))
        atTop
        (nhds L) := by
    -- Proof comment: subtract the convergent correction-plus-remainder block from the fixed
    -- endpoint increment to isolate the first-order dyadic integral sum.
    have hconst :
        Tendsto (fun _ : ℕ ↦ F (X T) - F (X 0)) atTop (nhds (F (X T) - F (X 0))) :=
      tendsto_const_nhds
    simpa [L] using hconst.sub hsum
  have hrewrite :
      (fun n ↦
        F (X T) - F (X 0) -
          ((F (X T) - F (X 0) -
              dyadicMultidimensionalItoApproximationUpTo F X T n -
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)) =
        fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n := by
    funext n
    ring
  have hlim' :
      Tendsto (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n) atTop (nhds L) := by
    simpa [hrewrite] using hlim
  have hcanon :
      pathwiseMultidimensionalItoIntegral F X T = L :=
    pathwiseMultidimensionalItoIntegral_eq_of_tendsto F X T hlim'
  -- Proof comment: rewrite the concrete limit through the canonical `limUnder` definition of the
  -- multidimensional pathwise Itô integral.
  simpa [hcanon] using hlim

-- Proof sketch: expand the second-order Taylor formula of `F` along the dyadic increments of the
-- vector path `X`, identify the first-order term with the limit of the dyadic gradient sums, and
-- collect the second-order contributions into the named quadratic-covariation correction object
-- `pathwiseMultidimensionalItoCorrection F X T`.
/-- If `X ∈ 𝒞_qv^d` and `F ∈ C²(ℝ^d)`, then the pathwise multidimensional Itô formula holds with
the named quadratic-covariation correction term `pathwiseMultidimensionalItoCorrection F X T`. -/
theorem pathwiseMultidimensionalItoFormula_eq_canonicalCorrection
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        pathwiseMultidimensionalItoCorrection F X T := by
  -- Route correction: a coordinatewise scalar-Itô reduction does not close the theorem because
  -- each weight `∂[i] F (X t)` depends on the full state `X t`.
  have hR :
      Tendsto
        (fun n ↦
          F (X T) - F (X 0) -
            dyadicMultidimensionalItoApproximationUpTo F X T n -
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
        atTop
        (nhds 0) :=
    tendsto_dyadicMultidimensionalItoTaylorRemainder F hf X hX T
  have hIto :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoApproximationUpTo F X T n)
        atTop
        (nhds (pathwiseMultidimensionalItoIntegral F X T)) :=
    tendsto_dyadicMultidimensionalItoApproximationUpTo F hf X hX T
  have hCorr :
      Tendsto
        (fun n ↦ dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)
        atTop
        (nhds (pathwiseMultidimensionalItoCorrection F X T)) :=
    pathwiseMultidimensionalItoCorrection_spec F hf X hX T
  have hsum :
      Tendsto
        (fun n ↦
          (F (X T) - F (X 0) -
              dyadicMultidimensionalItoApproximationUpTo F X T n -
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
            (dyadicMultidimensionalItoApproximationUpTo F X T n +
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n))
        atTop
        (nhds
          (pathwiseMultidimensionalItoIntegral F X T +
            pathwiseMultidimensionalItoCorrection F X T)) := by
    -- Proof comment: add the vanishing Taylor remainder back to the convergent first- and
    -- second-order dyadic sums.
    simpa [add_assoc] using hR.add (hIto.add hCorr)
  have hconst :
      (fun n ↦
        (F (X T) - F (X 0) -
            dyadicMultidimensionalItoApproximationUpTo F X T n -
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
          (dyadicMultidimensionalItoApproximationUpTo F X T n +
            dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n)) =
        fun _ ↦ F (X T) - F (X 0) := by
    funext n
    ring
  have hconstT :
      Tendsto
        (fun n ↦
          (F (X T) - F (X 0) -
              dyadicMultidimensionalItoApproximationUpTo F X T n -
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n) +
            (dyadicMultidimensionalItoApproximationUpTo F X T n +
              dyadicMultidimensionalItoCorrectionApproximationUpTo F X T n))
        atTop
        (nhds (F (X T) - F (X 0))) := by
    rw [hconst]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hconstT hsum

/-- Helper for Theorem 25.30: with constant weight `1`, the canonical pathwise
quadratic-covariation integral recovers the chosen quadratic covariation path. -/
theorem pathwiseQuadraticCovariationIntegral_one_eq
    {Y Z : PathSpace} {cov : PathwiseProcess}
    (hcov : HasQuadraticCovariationAlong Y Z cov) :
    pathwiseQuadraticCovariationIntegral (fun _ ↦ (1 : ℝ)) Y Z = cov := by
  ext T
  -- The constant-weight dyadic sums are exactly the defining mixed partition sums from `hcov`.
  apply pathwiseQuadraticCovariationIntegral_eq_of_tendsto
  simpa [dyadicQuadraticCovariationIntegralApproximationUpTo_def, dyadic_quadratic_covariation_sum,
    partitionQuadraticCovariationSum] using
    (HasQuadraticCovariationAlong.tendsto_partition_sum hcov T)

/-- Helper for Theorem 25.30: integrating the constant weight `1` against a signed Stieltjes
measure on `[0,T]` recovers the signed mass of that interval. -/
private theorem signedLebesgueStieltjesIntegralUpTo_one_eq_apply
    (μ : SignedMeasure ℝ) (T : NNReal) :
    signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) μ T =
      μ (Set.Icc (0 : ℝ) T) := by
  -- Proof comment: expand the Jordan decomposition formula and evaluate the constant integrals as
  -- the real masses of the positive and negative Jordan parts on the same interval.
  rw [signedLebesgueStieltjesIntegralUpTo_eq]
  have happly :
      μ.toJordanDecomposition.toSignedMeasure (Set.Icc (0 : ℝ) T) =
        μ (Set.Icc (0 : ℝ) T) :=
    congrArg (fun s : SignedMeasure ℝ => s (Set.Icc (0 : ℝ) T))
      (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
  simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply, measureReal_def,
    measurableSet_Icc] using happly

/-- Helper for Theorem 25.30: mapping a measure on `NNReal` to `ℝ` along the coercion preserves the
real mass of the interval `[0,T]`. -/
private theorem mapNNRealMeasure_real_Icc_eq
    (μ : Measure NNReal) (T : NNReal) :
    (Measure.map ((↑) : NNReal → ℝ) μ).real (Set.Icc (0 : ℝ) T) =
      μ.real (Set.Icc 0 T) := by
  -- Proof comment: compute the mapped mass using the measurable embedding `NNReal → ℝ`.
  have hpre :
      ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
    ext x
    simp
  rw [measureReal_def, measureReal_def,
    Measure.map_apply NNReal.continuous_coe.measurable measurableSet_Icc]
  simp [hpre]

/-- Helper for Theorem 25.30: integrating the prefix indicator `1_[0,τ]` over `[0,T]` against a
measure recovers the interval mass `μ (Set.Icc 0 τ)` whenever `τ ≤ T`. -/
private theorem setIntegral_indicatorIcc_eq_intervalMass
    (μ : Measure ℝ) {τ T : ℝ} (hτT : τ ≤ T) :
    ∫ s in Set.Icc (0 : ℝ) T,
        Set.indicator (Set.Icc (0 : ℝ) τ) (fun _ ↦ (1 : ℝ)) s ∂μ =
      μ.real (Set.Icc (0 : ℝ) τ) := by
  have hinter :
      Set.Icc (0 : ℝ) T ∩ Set.Icc (0 : ℝ) τ = Set.Icc (0 : ℝ) τ := by
    ext s
    constructor
    · intro hs
      exact hs.2
    · intro hs
      exact ⟨⟨hs.1, le_trans hs.2 hτT⟩, hs⟩
  have hinter' :
      Set.Icc (0 : ℝ) τ ∩ Set.Icc (0 : ℝ) T = Set.Icc (0 : ℝ) τ := by
    rw [Set.inter_comm, hinter]
  -- Proof comment: collapse the outer interval restriction with the inner prefix indicator.
  calc
    ∫ s in Set.Icc (0 : ℝ) T,
        Set.indicator (Set.Icc (0 : ℝ) τ) (fun _ ↦ (1 : ℝ)) s ∂μ
        = ∫ s, Set.indicator (Set.Icc (0 : ℝ) τ) (fun _ ↦ (1 : ℝ)) s
            ∂(μ.restrict (Set.Icc (0 : ℝ) T)) := by
          rfl
    _ = ∫ s in Set.Icc (0 : ℝ) τ, (1 : ℝ) ∂(μ.restrict (Set.Icc (0 : ℝ) T)) := by
          rw [MeasureTheory.integral_indicator measurableSet_Icc]
    _ = ∫ s in Set.Icc (0 : ℝ) τ, (1 : ℝ) ∂μ := by
          simp [Measure.restrict_restrict, hinter']
    _ = μ.real (Set.Icc (0 : ℝ) τ) := by
          rw [integral_const, measureReal_restrict_apply_univ]
          simp [smul_eq_mul]

/-- Helper for Theorem 25.30: integrating the prefix indicator `1_[0,τ]` against a signed
Stieltjes measure on `[0,T]` recovers the anchored interval mass `μ (Set.Icc 0 τ)` whenever
`τ ≤ T`. -/
private theorem signedLebesgueStieltjesIntegralUpTo_indicatorIcc_eq_apply
    (μ : SignedMeasure ℝ) {τ T : NNReal} (hτT : τ ≤ T) :
    signedLebesgueStieltjesIntegralUpTo
        (Set.indicator (Set.Icc (0 : ℝ) (τ : ℝ)) (fun _ ↦ (1 : ℝ)))
        μ
        T =
      μ (Set.Icc (0 : ℝ) τ) := by
  rw [signedLebesgueStieltjesIntegralUpTo_eq,
    setIntegral_indicatorIcc_eq_intervalMass (μ := μ.toJordanDecomposition.posPart)
      (τ := (τ : ℝ)) (T := (T : ℝ)) (show (τ : ℝ) ≤ T by exact_mod_cast hτT),
    setIntegral_indicatorIcc_eq_intervalMass (μ := μ.toJordanDecomposition.negPart)
      (τ := (τ : ℝ)) (T := (T : ℝ)) (show (τ : ℝ) ≤ T by exact_mod_cast hτT)]
  -- Proof comment: the remaining difference of Jordan masses is the signed interval mass.
  have happly :
      μ.toJordanDecomposition.toSignedMeasure (Set.Icc (0 : ℝ) τ) =
        μ (Set.Icc (0 : ℝ) τ) :=
    congrArg (fun s : SignedMeasure ℝ => s (Set.Icc (0 : ℝ) τ))
      (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
  simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply, measureReal_def,
    measurableSet_Icc] using happly

/-- Helper for Theorem 25.30: on the half-line, the real mass of `Set.Ioc a b` is the difference
of the anchored interval masses `μ (Set.Icc 0 b)` and `μ (Set.Icc 0 a)`. -/
private theorem measureReal_Ioc_eq_sub_Icc
    (μ : Measure ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hfinite : μ (Set.Icc (0 : ℝ) b) ≠ ⊤) :
    μ.real (Set.Ioc a b) =
      μ.real (Set.Icc (0 : ℝ) b) - μ.real (Set.Icc (0 : ℝ) a) := by
  have hunion : Set.Icc (0 : ℝ) b = Set.Icc (0 : ℝ) a ∪ Set.Ioc a b := by
    ext x
    constructor
    · intro hx
      by_cases hxa : x ≤ a
      · exact Or.inl ⟨hx.1, hxa⟩
      · exact Or.inr ⟨lt_of_not_ge hxa, hx.2⟩
    · intro hx
      rcases hx with hx | hx
      · exact ⟨hx.1, le_trans hx.2 hab⟩
      · exact ⟨le_trans ha (le_of_lt hx.1), hx.2⟩
  have hdisj : Disjoint (Set.Icc (0 : ℝ) a) (Set.Ioc a b) := by
    rw [Set.disjoint_left]
    intro x hxIcc hxIoc
    exact (not_lt_of_ge hxIcc.2) hxIoc.1
  have hIccFinite : μ (Set.Icc (0 : ℝ) a) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfinite)
    exact measure_mono fun x hx ↦ ⟨hx.1, le_trans hx.2 hab⟩
  have hIocFinite : μ (Set.Ioc a b) ≠ ⊤ := by
    refine ne_of_lt <| lt_of_le_of_lt ?_ (lt_top_iff_ne_top.2 hfinite)
    exact measure_mono fun x hx ↦ ⟨le_trans ha (le_of_lt hx.1), hx.2⟩
  have hmass :
      μ.real (Set.Icc (0 : ℝ) b) =
        μ.real (Set.Icc (0 : ℝ) a) + μ.real (Set.Ioc a b) := by
    have hmassUnion :
        μ.real (Set.Icc (0 : ℝ) a ∪ Set.Ioc a b) =
          μ.real (Set.Icc (0 : ℝ) a) + μ.real (Set.Ioc a b) := by
      simpa using
        (measureReal_union₀ (μ := μ) (s := Set.Icc (0 : ℝ) a) (t := Set.Ioc a b)
          measurableSet_Ioc.nullMeasurableSet
          hdisj.aedisjoint
          hIccFinite
          hIocFinite)
    simpa [hunion] using hmassUnion
  -- Proof comment: solve the finite-additivity identity for the interval cell mass.
  linarith

/-- Helper for Theorem 25.30: on the half-line, a signed interval mass on `Set.Ioc a b` is the
difference of the anchored masses on `Set.Icc 0 b` and `Set.Icc 0 a`. -/
private theorem signedMeasure_Ioc_eq_sub_Icc
    (μ : SignedMeasure ℝ) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    μ (Set.Ioc a b) =
      μ (Set.Icc (0 : ℝ) b) - μ (Set.Icc (0 : ℝ) a) := by
  have hioc :
      μ (Set.Ioc a b) =
        μ.toJordanDecomposition.posPart.real (Set.Ioc a b) -
          μ.toJordanDecomposition.negPart.real (Set.Ioc a b) := by
    have happly :
        μ.toJordanDecomposition.toSignedMeasure (Set.Ioc a b) =
          μ (Set.Ioc a b) :=
      congrArg (fun s : SignedMeasure ℝ => s (Set.Ioc a b))
        (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
    simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply,
      measureReal_def, measurableSet_Ioc] using happly.symm
  have hiccb :
      μ (Set.Icc (0 : ℝ) b) =
        μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) b) -
          μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) b) := by
    have happly :
        μ.toJordanDecomposition.toSignedMeasure (Set.Icc (0 : ℝ) b) =
          μ (Set.Icc (0 : ℝ) b) :=
      congrArg (fun s : SignedMeasure ℝ => s (Set.Icc (0 : ℝ) b))
        (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
    simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply,
      measureReal_def, measurableSet_Icc] using happly.symm
  have hicca :
      μ (Set.Icc (0 : ℝ) a) =
        μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) a) -
          μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) a) := by
    have happly :
        μ.toJordanDecomposition.toSignedMeasure (Set.Icc (0 : ℝ) a) =
          μ (Set.Icc (0 : ℝ) a) :=
      congrArg (fun s : SignedMeasure ℝ => s (Set.Icc (0 : ℝ) a))
        (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
    simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply,
      measureReal_def, measurableSet_Icc] using happly.symm
  have hpos :
      μ.toJordanDecomposition.posPart.real (Set.Ioc a b) =
        μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) b) -
          μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) a) :=
    measureReal_Ioc_eq_sub_Icc (μ := μ.toJordanDecomposition.posPart) ha hab (by simp)
  have hneg :
      μ.toJordanDecomposition.negPart.real (Set.Ioc a b) =
        μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) b) -
          μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) a) :=
    measureReal_Ioc_eq_sub_Icc (μ := μ.toJordanDecomposition.negPart) ha hab (by simp)
  calc
    μ (Set.Ioc a b)
        = μ.toJordanDecomposition.posPart.real (Set.Ioc a b) -
            μ.toJordanDecomposition.negPart.real (Set.Ioc a b) := hioc
    _ =
        (μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) b) -
            μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) a)) -
          (μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) b) -
            μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) a)) := by
      rw [hpos, hneg]
    _ =
        (μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) b) -
            μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) b)) -
          (μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) a) -
            μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) a)) := by
      ring
    _ = μ (Set.Icc (0 : ℝ) b) - μ (Set.Icc (0 : ℝ) a) := by
      rw [← hiccb, ← hicca]

/-- Helper for Theorem 25.30: on a finite measure, the prefix indicator `1_[0,τ]` is integrable.
-/
private theorem integrable_indicatorIcc_one
    (μ : Measure ℝ) [IsFiniteMeasure μ] (τ : ℝ) :
    Integrable (Set.indicator (Set.Icc (0 : ℝ) τ) (fun _ ↦ (1 : ℝ))) μ := by
  -- Proof comment: the integrand is a bounded measurable indicator on a finite measure space.
  simpa using ((integrable_const (1 : ℝ)).indicator measurableSet_Icc)

/-- Helper for Theorem 25.30: the dyadic coarse left-step staircase written as a constant plus
prefix indicators on the real interval `[0,T]`. -/
private noncomputable def dyadicPrefixStaircase
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) : ℝ → ℝ :=
  fun s ↦
    H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1)) +
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) fun i ↦
        (H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))) *
          Set.indicator (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
            (fun _ ↦ (1 : ℝ)) s

/-- Helper for Theorem 25.30: the dyadic prefix staircase is a measurable real-valued function.
-/
private theorem measurable_dyadicPrefixStaircase
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) :
    Measurable (dyadicPrefixStaircase H T n) := by
  -- Proof comment: the staircase is a constant plus a finite sum of measurable indicators.
  unfold dyadicPrefixStaircase
  refine measurable_const.add ?_
  refine Finset.measurable_sum _ ?_
  intro i hi
  exact measurable_const.mul (measurable_const.indicator measurableSet_Icc)

/-- Helper for Theorem 25.30: on `[0,T]`, the real-valued prefix staircase is the dyadic
`dyadicCoarseIccStep` pulled back along the coercion `NNReal → ℝ`. -/
private theorem dyadicPrefixStaircase_eq_coarseIccStepOnIcc
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    dyadicPrefixStaircase H T n s = dyadicCoarseIccStep H n T s.toNNReal := by
  have hs0 : 0 ≤ s := hs.1
  unfold dyadicPrefixStaircase dyadicCoarseIccStep
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  have hmem :
      s ∈ Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ) ↔
        s.toNNReal ∈ Set.Icc 0 (dyadicPartitionSequence n (i + 1)) := by
    constructor
    · intro hsIcc
      refine ⟨bot_le, ?_⟩
      have hs_le :
          (s.toNNReal : ℝ) ≤ (dyadicPartitionSequence n (i + 1) : ℝ) := by
        simpa [Real.toNNReal_of_nonneg hsIcc.1] using hsIcc.2
      exact_mod_cast hs_le
    · intro hsIcc
      refine ⟨hs0, ?_⟩
      have hs_le : (s.toNNReal : ℝ) ≤ (dyadicPartitionSequence n (i + 1) : ℝ) := by
        exact_mod_cast hsIcc.2
      simpa [Real.toNNReal_of_nonneg hs0] using hs_le
  by_cases hsIcc : s ∈ Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)
  · have hsIccNN : s.toNNReal ∈ Set.Icc 0 (dyadicPartitionSequence n (i + 1)) :=
      hmem.mp hsIcc
    simp [hsIcc, hsIccNN]
  · have hsIccNN : s.toNNReal ∉ Set.Icc 0 (dyadicPartitionSequence n (i + 1)) := by
      intro hs'
      exact hsIcc (hmem.mpr hs')
    simp [hsIcc, hsIccNN]

/-- Helper for Theorem 25.30: on `[0,T]`, the dyadic prefix staircase samples `H` at the
predecessor point of the evaluation time in the `n`-th dyadic row. -/
private theorem dyadicPrefixStaircase_eq_partitionPredecessorPoint
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) T) :
    dyadicPrefixStaircase H T n s =
      H (dyadicPartitionPredecessorPoint n s.toNNReal) := by
  have hsNN : s.toNNReal ∈ Set.Icc 0 T := by
    refine ⟨bot_le, ?_⟩
    have hs_le : (s.toNNReal : ℝ) ≤ T := by
      simpa [Real.toNNReal_of_nonneg hs.1] using hs.2
    exact_mod_cast hs_le
  -- Proof comment: transport the real staircase to the canonical `dyadicCoarseIccStep`, then reuse the
  -- existing predecessor-point description from Remark 21.62.
  rw [dyadicPrefixStaircase_eq_coarseIccStepOnIcc H T n hs]
  simpa using dyadicCoarseIccStep_eq_partitionPredecessorValue H n T s.toNNReal hsNN

/-- Helper for Theorem 25.30: the predecessor dyadic partition points converge to the evaluation
time because they stay within one mesh width and the dyadic mesh tends to zero. -/
private theorem tendsto_partitionPredecessorPoint_dyadic
    (T : NNReal) :
    Tendsto (fun n : ℕ ↦ dyadicPartitionPredecessorPoint n T) atTop (nhds T) := by
  refine Metric.tendsto_atTop.mpr ?_
  intro ε hε
  let ε' : ℝ := ε / 2
  have hε' : 0 < ε' := by
    dsimp [ε']
    linarith
  have hmesh :
      ∀ᶠ n in atTop, partitionMesh dyadicPartitionSequence n ≤ ENNReal.ofReal ε' := by
    rcases
        (ENNReal.tendsto_atTop_zero.mp
          Definition2158.tendsto_partitionMesh_dyadicPartitionSequence)
          (ENNReal.ofReal ε') (ENNReal.ofReal_pos.mpr hε') with
      ⟨N, hN⟩
    exact Filter.eventually_atTop.2 ⟨N, hN⟩
  rcases Filter.eventually_atTop.1 hmesh with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  have hedist :
      edist (dyadicPartitionPredecessorPoint n T) T ≤ ENNReal.ofReal ε' := by
    exact (dyadicPartitionPredecessorPointWithinMesh n T).trans (hN n hn)
  have hdist : dist (dyadicPartitionPredecessorPoint n T) T ≤ ε' := by
    exact (ENNReal.ofReal_le_ofReal_iff hε'.le).mp (by simpa [edist_dist] using hedist)
  calc
    dist (dyadicPartitionPredecessorPoint n T) T ≤ ε' := hdist
    _ < ε := by
      dsimp [ε']
      linarith

/-- Helper for Theorem 25.30: integrating the dyadic prefix staircase against a finite measure on
`[0,T]` expands into the corresponding anchored interval masses. -/
private theorem setIntegral_dyadicPrefixStaircase_eq_massSum
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) (μ : Measure ℝ)
    (hμfinite : μ (Set.Icc (0 : ℝ) T) ≠ ⊤) :
    ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s ∂μ =
      H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1)) *
          μ.real (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) fun i ↦
          (H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))) *
            μ.real (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
  let N := partitionBoundIndex dyadicPartitionSequence n T
  let ν : Measure ℝ := μ.restrict (Set.Icc (0 : ℝ) T)
  let cLast : ℝ := H (dyadicPartitionSequence n (N - 1))
  let coeff : ℕ → ℝ := fun i ↦
    H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using (lt_top_iff_ne_top.mpr hμfinite)
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  have hconst :
      Integrable (fun _ : ℝ ↦ cLast) ν := by
    exact integrable_const cLast
  have htermInt :
      ∀ i ∈ Finset.range (N - 1),
        Integrable
          (fun s : ℝ ↦
            coeff i *
              Set.indicator
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s)
          ν := by
    intro i hi
    exact ((integrable_const (1 : ℝ)).indicator measurableSet_Icc).const_mul (coeff i)
  have hsum :
      Integrable
        (fun s : ℝ ↦
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i *
              Set.indicator
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s)
        ν := by
    exact integrable_finset_sum _ htermInt
  have hτ :
      ∀ i ∈ Finset.range (N - 1),
        (dyadicPartitionSequence n (i + 1) : ℝ) ≤ T := by
    intro i hi
    have hi_lt : i < N - 1 := Finset.mem_range.mp hi
    have hi_succ_lt : i + 1 < (N - 1) + 1 := Nat.succ_lt_succ hi_lt
    have hN : 0 < N := by
      exact lt_of_lt_of_le (Nat.zero_lt_succ i)
        (le_trans (Nat.succ_le_of_lt hi_lt) (Nat.sub_le _ _))
    have hN_eq : (N - 1) + 1 = N := Nat.sub_add_cancel (Nat.one_le_of_lt hN)
    have hi' : i + 1 < N := by
      simpa [hN_eq] using hi_succ_lt
    exact le_of_lt (dyadicPartition_lt_time_of_lt_boundIndex n hi')
  have htermEval :
      ∀ i ∈ Finset.range (N - 1),
        ∫ s,
            coeff i *
              Set.indicator
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s ∂ν =
          coeff i * μ.real (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
    intro i hi
    calc
      ∫ s,
          coeff i *
            Set.indicator
              (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
              (fun _ ↦ (1 : ℝ)) s ∂ν
          = coeff i *
              ∫ s,
                Set.indicator
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s ∂ν := by
              rw [integral_const_mul]
      _ = coeff i *
            ∫ s in Set.Icc (0 : ℝ) T,
              Set.indicator
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                (fun _ ↦ (1 : ℝ)) s ∂μ := by
              rfl
      _ = coeff i * μ.real (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
              rw [setIntegral_indicatorIcc_eq_intervalMass (μ := μ) (hτ i hi)]
  -- Proof comment: expand the staircase into its constant part and finitely many prefix
  -- indicators, then evaluate each basis integral by the anchored interval-mass formula.
  calc
    ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s ∂μ
        = ∫ s,
            (fun t ↦
              cLast +
                Finset.sum (Finset.range (N - 1)) fun i ↦
                  coeff i *
                    Set.indicator
                      (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                      (fun _ ↦ (1 : ℝ)) t) s ∂ν := by
            rfl
    _ = ∫ s, (fun _ : ℝ ↦ cLast) s ∂ν +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s ∂ν := by
            change
              ∫ s,
                ((fun _ : ℝ ↦ cLast) s +
                  Finset.sum (Finset.range (N - 1)) fun i ↦
                    coeff i *
                      Set.indicator
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                        (fun _ ↦ (1 : ℝ)) s) ∂ν =
                _ + _
            rw [integral_add hconst hsum]
    _ = cLast * μ.real (Set.Icc (0 : ℝ) T) +
          ∫ s,
            Finset.sum (Finset.range (N - 1)) fun i ↦
              coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s ∂ν := by
            rw [integral_const, measureReal_restrict_apply_univ]
            simp [ν, cLast, smul_eq_mul, mul_comm]
    _ = cLast * μ.real (Set.Icc (0 : ℝ) T) +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            ∫ s,
              coeff i *
                Set.indicator
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))
                  (fun _ ↦ (1 : ℝ)) s ∂ν := by
            rw [integral_finset_sum _ htermInt]
    _ = cLast * μ.real (Set.Icc (0 : ℝ) T) +
          Finset.sum (Finset.range (N - 1)) fun i ↦
            coeff i * μ.real (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
            congr 1
            refine Finset.sum_congr rfl ?_
            intro i hi
            exact htermEval i hi
    _ = H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1)) *
          μ.real (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) fun i ↦
          (H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))) *
            μ.real (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
            simp [N, cLast, coeff]

/-- Helper for Theorem 25.30: the dyadic prefix staircase satisfies the finite-level polarized
identity obtained from the anchored interval masses. -/
private theorem covariationIccMass_eq_polarizedDifference
    {covYY covZZ covYZ : PathSpace}
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        covYZ T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    {μAdd μSub : Measure NNReal}
    (hμAddMass :
      ∀ T : NNReal,
        covYY T + 2 * covYZ T + covZZ T =
          μAdd.real (Set.Icc 0 T))
    (hμSubMass :
      ∀ T : NNReal,
        covYY T - 2 * covYZ T + covZZ T =
          μSub.real (Set.Icc 0 T))
    (τ : NNReal) :
    covariationMeasure (Set.Icc (0 : ℝ) τ) =
      (1 / 4 : ℝ) *
        ((Measure.map ((↑) : NNReal → ℝ) μAdd).real (Set.Icc (0 : ℝ) τ) -
          (Measure.map ((↑) : NNReal → ℝ) μSub).real (Set.Icc (0 : ℝ) τ)) := by
  have hcov :
      covariationMeasure (Set.Icc (0 : ℝ) τ) = covYZ τ := by
    rw [hcovariationMeasure τ, signedLebesgueStieltjesIntegralUpTo_one_eq_apply]
  have hAddMap :
      (Measure.map ((↑) : NNReal → ℝ) μAdd).real (Set.Icc (0 : ℝ) τ) =
        covYY τ + 2 * covYZ τ + covZZ τ := by
    rw [mapNNRealMeasure_real_Icc_eq, ← hμAddMass τ]
  have hSubMap :
      (Measure.map ((↑) : NNReal → ℝ) μSub).real (Set.Icc (0 : ℝ) τ) =
        covYY τ - 2 * covYZ τ + covZZ τ := by
    rw [mapNNRealMeasure_real_Icc_eq, ← hμSubMass τ]
  -- Proof comment: after rewriting the signed interval mass as `covYZ τ`, polarization reduces
  -- the quarter-difference of the plus/minus square masses to the mixed covariation term.
  calc
    covariationMeasure (Set.Icc (0 : ℝ) τ) = covYZ τ := hcov
    _ =
      (1 / 4 : ℝ) *
        ((covYY τ + 2 * covYZ τ + covZZ τ) -
          (covYY τ - 2 * covYZ τ + covZZ τ)) := by
            ring
    _ =
      (1 / 4 : ℝ) *
        ((Measure.map ((↑) : NNReal → ℝ) μAdd).real (Set.Icc (0 : ℝ) τ) -
          (Measure.map ((↑) : NNReal → ℝ) μSub).real (Set.Icc (0 : ℝ) τ)) := by
            rw [hAddMap, hSubMap]

/-- Helper for Theorem 25.30: integrating the dyadic prefix staircase against a signed
Stieltjes measure on `[0,T]` expands into anchored signed interval masses. -/
private theorem signedLebesgueStieltjesIntegralUpTo_dyadicPrefixStaircase_eq_massSum
    (H : NNReal → ℝ) (T : NNReal) (n : ℕ) (μ : SignedMeasure ℝ) :
    signedLebesgueStieltjesIntegralUpTo
        (dyadicPrefixStaircase H T n)
        μ
        T =
      H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1)) *
          μ (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) fun i ↦
          (H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))) *
            μ (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
  let cLast : ℝ := by
    exact H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1))
  let coeff : ℕ → ℝ := fun i ↦
    H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))
  have hTmass :
      μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) T) -
          μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) T) =
        μ (Set.Icc (0 : ℝ) T) := by
    have happly :
        μ.toJordanDecomposition.toSignedMeasure (Set.Icc (0 : ℝ) T) =
          μ (Set.Icc (0 : ℝ) T) :=
      congrArg (fun s : SignedMeasure ℝ => s (Set.Icc (0 : ℝ) T))
        (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
    simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply, measureReal_def,
      measurableSet_Icc] using happly
  have hImass :
      ∀ i : ℕ,
        μ.toJordanDecomposition.posPart.real
              (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) -
            μ.toJordanDecomposition.negPart.real
              (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) =
          μ (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
    intro i
    have happly :
        μ.toJordanDecomposition.toSignedMeasure
            (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) =
          μ (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) :=
      congrArg
        (fun s : SignedMeasure ℝ =>
          s (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))
        (SignedMeasure.toSignedMeasure_toJordanDecomposition μ)
    simpa [JordanDecomposition.toSignedMeasure, Measure.toSignedMeasure_sub_apply, measureReal_def,
      measurableSet_Icc] using happly
  -- Proof comment: evaluate the positive and negative Jordan parts by the ordinary staircase
  -- mass-sum formula and recombine each anchored interval mass back into the signed mass of `μ`.
  rw [signedLebesgueStieltjesIntegralUpTo_eq,
    setIntegral_dyadicPrefixStaircase_eq_massSum
      (μ := μ.toJordanDecomposition.posPart) (hμfinite := measure_ne_top _ _),
    setIntegral_dyadicPrefixStaircase_eq_massSum
      (μ := μ.toJordanDecomposition.negPart) (hμfinite := measure_ne_top _ _)]
  calc
    (cLast * μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
          coeff i *
            μ.toJordanDecomposition.posPart.real
              (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) -
        (cLast * μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) T) +
          Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
            coeff i *
              μ.toJordanDecomposition.negPart.real
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))))
        =
      cLast *
          (μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) T) -
            μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) T)) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
          coeff i *
            (μ.toJordanDecomposition.posPart.real
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) -
              μ.toJordanDecomposition.negPart.real
                (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))) := by
          have hsum :
              Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦
                    coeff i *
                      μ.toJordanDecomposition.posPart.real
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) -
                Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦
                    coeff i *
                      μ.toJordanDecomposition.negPart.real
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) =
              Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                (fun i ↦
                  coeff i *
                    (μ.toJordanDecomposition.posPart.real
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) -
                      μ.toJordanDecomposition.negPart.real
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))) := by
            rw [← Finset.sum_sub_distrib]
            refine Finset.sum_congr rfl ?_
            intro i hi
            ring
          calc
            (cLast * μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) T) +
                Finset.sum
                  (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦
                    coeff i *
                      μ.toJordanDecomposition.posPart.real
                        (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))) -
                (cLast * μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) T) +
                  Finset.sum
                    (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                    (fun i ↦
                      coeff i *
                        μ.toJordanDecomposition.negPart.real
                          (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))) =
              cLast *
                  (μ.toJordanDecomposition.posPart.real (Set.Icc (0 : ℝ) T) -
                    μ.toJordanDecomposition.negPart.real (Set.Icc (0 : ℝ) T)) +
                (Finset.sum
                    (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                    (fun i ↦
                      coeff i *
                        μ.toJordanDecomposition.posPart.real
                          (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) -
                  Finset.sum
                    (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                    (fun i ↦
                      coeff i *
                        μ.toJordanDecomposition.negPart.real
                          (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)))) := by
                ring
            _ = _ := by rw [hsum]
    _ =
      cLast * μ (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
          coeff i * μ (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) := by
          simp [hTmass, hImass]
    _ = H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1)) *
          μ (Set.Icc (0 : ℝ) T) +
        Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) fun i ↦
          (H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))) *
            μ (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) := by
          simp [cLast, coeff]

private theorem dyadicPrefixStaircase_polarizedDifference
    (H : NNReal → ℝ)
    {covYY covZZ covYZ : PathSpace}
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        covYZ T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    {μAdd μSub : Measure NNReal}
    (hμAddMass :
      ∀ T : NNReal,
        covYY T + 2 * covYZ T + covZZ T =
          μAdd.real (Set.Icc 0 T))
    (hμSubMass :
      ∀ T : NNReal,
        covYY T - 2 * covYZ T + covZZ T =
          μSub.real (Set.Icc 0 T))
    (hμAddFinite : ∀ T : NNReal, μAdd (Set.Icc 0 T) ≠ ⊤)
    (hμSubFinite : ∀ T : NNReal, μSub (Set.Icc 0 T) ≠ ⊤)
    (T : NNReal) (n : ℕ) :
    signedLebesgueStieltjesIntegralUpTo
        (dyadicPrefixStaircase H T n)
        covariationMeasure
        T =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc (0 : ℝ) T,
            dyadicPrefixStaircase H T n s ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
          (∫ s in Set.Icc (0 : ℝ) T,
            dyadicPrefixStaircase H T n s ∂(Measure.map ((↑) : NNReal → ℝ) μSub))) := by
  let cLast : ℝ := by
    exact H (dyadicPartitionSequence n (partitionBoundIndex dyadicPartitionSequence n T - 1))
  let coeff : ℕ → ℝ := fun i ↦
    H (dyadicPartitionSequence n i) - H (dyadicPartitionSequence n (i + 1))
  let addMass : NNReal → ℝ := fun τ ↦
    (Measure.map ((↑) : NNReal → ℝ) μAdd).real (Set.Icc (0 : ℝ) τ)
  let subMass : NNReal → ℝ := fun τ ↦
    (Measure.map ((↑) : NNReal → ℝ) μSub).real (Set.Icc (0 : ℝ) τ)
  have hμAddMapFinite :
      (Measure.map ((↑) : NNReal → ℝ) μAdd) (Set.Icc (0 : ℝ) T) ≠ ⊤ := by
    have hpre :
        ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
      ext x
      simp
    rw [Measure.map_apply measurable_coe_nnreal_real measurableSet_Icc]
    simpa [hpre] using hμAddFinite T
  have hμSubMapFinite :
      (Measure.map ((↑) : NNReal → ℝ) μSub) (Set.Icc (0 : ℝ) T) ≠ ⊤ := by
    have hpre :
        ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
      ext x
      simp
    rw [Measure.map_apply measurable_coe_nnreal_real measurableSet_Icc]
    simpa [hpre] using hμSubFinite T
  have hTop :
      covariationMeasure (Set.Icc (0 : ℝ) T) =
        (1 / 4 : ℝ) * (addMass T - subMass T) := by
    simpa [addMass, subMass] using
      covariationIccMass_eq_polarizedDifference
        (covariationMeasure := covariationMeasure)
        (covYY := covYY) (covZZ := covZZ) (covYZ := covYZ)
        hcovariationMeasure hμAddMass hμSubMass T
  have hTerm :
      ∀ i : ℕ,
        covariationMeasure (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ)) =
          (1 / 4 : ℝ) *
            (addMass (dyadicPartitionSequence n (i + 1)) -
              subMass (dyadicPartitionSequence n (i + 1))) := by
    intro i
    simpa [addMass, subMass] using
      covariationIccMass_eq_polarizedDifference
        (covariationMeasure := covariationMeasure)
        (covYY := covYY) (covZZ := covZZ) (covYZ := covYZ)
        hcovariationMeasure hμAddMass hμSubMass (dyadicPartitionSequence n (i + 1))
  have hsum :
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
        coeff i * covariationMeasure (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) =
      Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1)) (fun i ↦
        coeff i *
          ((1 / 4 : ℝ) *
            (addMass (dyadicPartitionSequence n (i + 1)) -
              subMass (dyadicPartitionSequence n (i + 1))))) := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    rw [hTerm i]
  -- Proof comment: rewrite the signed staircase integral and both mapped-measure staircase
  -- integrals by the same anchored-mass basis and then apply polarization coefficientwise.
  rw [signedLebesgueStieltjesIntegralUpTo_dyadicPrefixStaircase_eq_massSum,
    setIntegral_dyadicPrefixStaircase_eq_massSum
      (μ := Measure.map ((↑) : NNReal → ℝ) μAdd) (hμfinite := hμAddMapFinite),
    setIntegral_dyadicPrefixStaircase_eq_massSum
      (μ := Measure.map ((↑) : NNReal → ℝ) μSub) (hμfinite := hμSubMapFinite)]
  have hmass :
      cLast * covariationMeasure (Set.Icc (0 : ℝ) T) +
          Finset.sum
            (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
            (fun i ↦
              coeff i *
                covariationMeasure
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) =
        (1 / 4 : ℝ) *
          ((cLast * addMass T +
                Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦ coeff i * addMass (dyadicPartitionSequence n (i + 1)))) -
            (cLast * subMass T +
                Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦ coeff i * subMass (dyadicPartitionSequence n (i + 1))))) := by
    calc
      cLast * covariationMeasure (Set.Icc (0 : ℝ) T) +
          Finset.sum
            (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
            (fun i ↦
              coeff i *
                covariationMeasure
                  (Set.Icc (0 : ℝ) (dyadicPartitionSequence n (i + 1) : ℝ))) =
        cLast * ((1 / 4 : ℝ) * (addMass T - subMass T)) +
          Finset.sum
            (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
            (fun i ↦
              coeff i *
                ((1 / 4 : ℝ) *
                  (addMass (dyadicPartitionSequence n (i + 1)) -
                    subMass (dyadicPartitionSequence n (i + 1))))) := by
            rw [hTop, hsum]
      _ =
        (1 / 4 : ℝ) *
          ((cLast * addMass T +
                Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦ coeff i * addMass (dyadicPartitionSequence n (i + 1)))) -
            (cLast * subMass T +
                Finset.sum (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                  (fun i ↦ coeff i * subMass (dyadicPartitionSequence n (i + 1))))) := by
            calc
              cLast * ((1 / 4 : ℝ) * (addMass T - subMass T)) +
                  Finset.sum
                    (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                    (fun i ↦
                      coeff i *
                        ((1 / 4 : ℝ) *
                          (addMass (dyadicPartitionSequence n (i + 1)) -
                            subMass (dyadicPartitionSequence n (i + 1))))) =
                cLast * addMass T * (1 / 4 : ℝ) +
                  cLast * subMass T * (-1 / 4 : ℝ) +
                  Finset.sum
                    (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                    (fun i ↦
                      coeff i * addMass (dyadicPartitionSequence n (i + 1)) * (1 / 4 : ℝ) +
                        coeff i * subMass (dyadicPartitionSequence n (i + 1)) * (-1 / 4 : ℝ)) := by
                  ring_nf
              _ =
                cLast * addMass T * (1 / 4 : ℝ) +
                  cLast * subMass T * (-1 / 4 : ℝ) +
                  (Finset.sum
                      (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                      (fun i ↦ coeff i * addMass (dyadicPartitionSequence n (i + 1)))) *
                    (1 / 4 : ℝ) +
                  (Finset.sum
                      (Finset.range (partitionBoundIndex dyadicPartitionSequence n T - 1))
                      (fun i ↦ coeff i * subMass (dyadicPartitionSequence n (i + 1)))) *
                    (-1 / 4 : ℝ) := by
                  rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul]
                  ring_nf
              _ = _ := by
                  ring_nf
  simpa [cLast, coeff, addMass, subMass] using hmass

/-- Helper for Theorem 25.30: on `[0,T]`, the dyadic prefix staircases converge pointwise to the
continuous weight by predecessor-point convergence. -/
private theorem dyadicPrefixStaircase_tendsto_pointwise
    (H : NNReal → ℝ) (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (T : NNReal) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun n : ℕ ↦ dyadicPrefixStaircase H T n s) atTop (nhds (H s.toNNReal)) := by
  have hHNN : Continuous H := by
    -- Proof comment: the real-variable continuity assumption restricts to continuity of `H` on
    -- `NNReal`.
    convert hH.comp NNReal.continuous_coe using 1
    ext t
    simp
  have hrewrite :
      (fun n : ℕ ↦ dyadicPrefixStaircase H T n s) =
        fun n : ℕ ↦ H (dyadicPartitionPredecessorPoint n s.toNNReal) := by
    -- Proof comment: on `[0, T]`, each staircase value is the predecessor-point sample of `H`.
    funext n
    exact dyadicPrefixStaircase_eq_partitionPredecessorPoint H T n hs
  rw [hrewrite]
  -- Proof comment: the predecessor points converge back to `s.toNNReal`, and continuity of `H`
  -- transports that convergence to the function values.
  exact hHNN.continuousAt.tendsto.comp
    (tendsto_partitionPredecessorPoint_dyadic s.toNNReal)

/-- Helper for Theorem 25.30: continuity on the compact interval `[0,T]` provides one common
dominating constant for the dyadic prefix staircases and for the limit weight. -/
private theorem dyadicPrefixStaircase_abs_le
    (H : NNReal → ℝ) (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (T : NNReal) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, |dyadicPrefixStaircase H T n s| ≤ C) ∧
      ∀ s ∈ Set.Icc (0 : ℝ) T, |H s.toNNReal| ≤ C := by
  have hHNN : Continuous H := by
    -- Proof comment: the real-variable continuity assumption restricts back to continuity of `H`
    -- on `NNReal`.
    convert hH.comp NNReal.continuous_coe using 1
    ext s
    simp
  obtain ⟨C, hC⟩ :
      ∃ C : ℝ, ∀ u ∈ Set.Icc (0 : NNReal) T, ‖H u‖ ≤ C :=
    (isCompact_Icc : IsCompact (Set.Icc (0 : NNReal) T)).exists_bound_of_continuousOn
      hHNN.continuousOn
  have hC_nonneg : 0 ≤ C := by
    have hzero : ‖H 0‖ ≤ C := hC 0 (by simp : (0 : NNReal) ∈ Set.Icc (0 : NNReal) T)
    exact le_trans (by simp) hzero
  refine ⟨C, hC_nonneg, ?_, ?_⟩
  · intro n s hs
    have hpred_mem :
        dyadicPartitionPredecessorPoint n s.toNNReal ∈ Set.Icc (0 : NNReal) T := by
      refine ⟨bot_le, ?_⟩
      have hs_le : (s.toNNReal : ℝ) ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs.1] using hs.2
      exact le_trans
        (dyadicPartitionPredecessorPoint_le_time n s.toNNReal)
        (by exact_mod_cast hs_le)
    -- Proof comment: each staircase value is a predecessor-point sample of `H`, and those
    -- predecessor points stay inside the same compact interval `[0,T]`.
    rw [dyadicPrefixStaircase_eq_partitionPredecessorPoint H T n hs]
    simpa [Real.norm_eq_abs] using hC _ hpred_mem
  · intro s hs
    have hsNN : s.toNNReal ∈ Set.Icc (0 : NNReal) T := by
      refine ⟨bot_le, ?_⟩
      have hs_le : (s.toNNReal : ℝ) ≤ T := by
        simpa [Real.toNNReal_of_nonneg hs.1] using hs.2
      exact_mod_cast hs_le
    simpa [Real.norm_eq_abs] using hC _ hsNN

/-- Helper for Theorem 25.30: against a finite measure on `Set.Icc (0 : ℝ) T`, the dyadic
prefix staircases converge in integral to the continuous weight. -/
private theorem tendsto_setIntegral_dyadicPrefixStaircase_of_continuous
    (H : NNReal → ℝ) (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (μ : Measure ℝ) (T : NNReal) (hμfinite : μ (Set.Icc (0 : ℝ) T) ≠ ⊤) :
    Tendsto
      (fun n ↦ ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s ∂μ)
      atTop
      (nhds (∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂μ)) := by
  let ν : Measure ℝ := μ.restrict (Set.Icc (0 : ℝ) T)
  have hν_univ_lt_top : ν Set.univ < ⊤ := by
    simpa [ν] using (lt_top_iff_ne_top.mpr hμfinite)
  letI : IsFiniteMeasure ν := ⟨hν_univ_lt_top⟩
  obtain ⟨C, hC_nonneg, hbound, _hlimitBound⟩ := dyadicPrefixStaircase_abs_le H hH T
  have hmeas :
      ∀ n : ℕ, AEStronglyMeasurable (fun s : ℝ ↦ dyadicPrefixStaircase H T n s) ν := by
    intro n
    exact (measurable_dyadicPrefixStaircase H T n).aestronglyMeasurable
  have hboundAE :
      ∀ n : ℕ, ∀ᵐ s ∂ν, ‖dyadicPrefixStaircase H T n s‖ ≤ (fun _ : ℝ ↦ C) s := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    simpa [Real.norm_eq_abs] using hbound n s hs
  have hlimAE :
      ∀ᵐ s ∂ν, Tendsto (fun n : ℕ ↦ dyadicPrefixStaircase H T n s) atTop (nhds (H s.toNNReal)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
    exact dyadicPrefixStaircase_tendsto_pointwise H hH T hs
  -- Proof comment: on the restricted finite measure `ν`, the dyadic staircases are uniformly
  -- bounded and converge pointwise on the whole support, so dominated convergence identifies the
  -- limiting integral.
  simpa [ν] using
    (MeasureTheory.tendsto_integral_of_dominated_convergence
      (fun _ : ℝ ↦ C) hmeas (integrable_const C) hboundAE hlimAE)

/-- Helper for Theorem 25.30: a continuous weight together with a signed-measure realization of a
quadratic covariation path can be rewritten through the polarization measures of the self- and
mixed-covariation witnesses. -/
private theorem signedLebesgueStieltjesIntegralUpTo_eq_polarizedDifference
    (H : NNReal → ℝ)
    {covYY covZZ covYZ : PathSpace}
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        covYZ T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    {μAdd μSub : Measure NNReal}
    (hμAddMass :
      ∀ T : NNReal,
        covYY T + 2 * covYZ T + covZZ T =
          μAdd.real (Set.Icc 0 T))
    (hμSubMass :
      ∀ T : NNReal,
        covYY T - 2 * covYZ T + covZZ T =
          μSub.real (Set.Icc 0 T))
    (hμAddFinite : ∀ T : NNReal, μAdd (Set.Icc 0 T) ≠ ⊤)
    (hμSubFinite : ∀ T : NNReal, μSub (Set.Icc 0 T) ≠ ⊤)
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (T : NNReal) :
    signedLebesgueStieltjesIntegralUpTo
        (fun s ↦ H s.toNNReal)
        covariationMeasure
        T =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
          ∫ s in Set.Icc 0 T, H s ∂μSub) := by
  have hμAddMapFinite :
      (Measure.map ((↑) : NNReal → ℝ) μAdd) (Set.Icc (0 : ℝ) T) ≠ ⊤ := by
    have hpre :
        ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
      ext x
      simp
    rw [Measure.map_apply measurable_coe_nnreal_real measurableSet_Icc]
    simpa [hpre] using hμAddFinite T
  have hμSubMapFinite :
      (Measure.map ((↑) : NNReal → ℝ) μSub) (Set.Icc (0 : ℝ) T) ≠ ⊤ := by
    have hpre :
        ((↑) : NNReal → ℝ) ⁻¹' Set.Icc (0 : ℝ) T = Set.Icc 0 T := by
      ext x
      simp
    rw [Measure.map_apply measurable_coe_nnreal_real measurableSet_Icc]
    simpa [hpre] using hμSubFinite T
  have hSignedLim :
      Tendsto
        (fun n ↦
          signedLebesgueStieltjesIntegralUpTo
            (dyadicPrefixStaircase H T n)
            covariationMeasure
            T)
        atTop
        (nhds
          (signedLebesgueStieltjesIntegralUpTo
            (fun s ↦ H s.toNNReal)
            covariationMeasure
            T)) := by
    -- Proof comment: apply dominated convergence separately to the positive and negative Jordan
    -- parts of the signed measure and then reassemble them by subtraction.
    have hPos :
        Tendsto
          (fun n ↦
            ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
              ∂covariationMeasure.toJordanDecomposition.posPart)
          atTop
          (nhds
            (∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
              ∂covariationMeasure.toJordanDecomposition.posPart)) :=
      tendsto_setIntegral_dyadicPrefixStaircase_of_continuous H hH
        covariationMeasure.toJordanDecomposition.posPart T (measure_ne_top _ _)
    have hNeg :
        Tendsto
          (fun n ↦
            ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
              ∂covariationMeasure.toJordanDecomposition.negPart)
          atTop
          (nhds
            (∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
              ∂covariationMeasure.toJordanDecomposition.negPart)) :=
      tendsto_setIntegral_dyadicPrefixStaircase_of_continuous H hH
        covariationMeasure.toJordanDecomposition.negPart T (measure_ne_top _ _)
    simpa [signedLebesgueStieltjesIntegralUpTo_eq] using hPos.sub hNeg
  have hAddLim :
      Tendsto
        (fun n ↦
          ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
            ∂(Measure.map ((↑) : NNReal → ℝ) μAdd))
        atTop
        (nhds
          (∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
            ∂(Measure.map ((↑) : NNReal → ℝ) μAdd))) :=
    tendsto_setIntegral_dyadicPrefixStaircase_of_continuous H hH
      (Measure.map ((↑) : NNReal → ℝ) μAdd) T hμAddMapFinite
  have hSubLim :
      Tendsto
        (fun n ↦
          ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
            ∂(Measure.map ((↑) : NNReal → ℝ) μSub))
        atTop
        (nhds
          (∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
            ∂(Measure.map ((↑) : NNReal → ℝ) μSub))) :=
    tendsto_setIntegral_dyadicPrefixStaircase_of_continuous H hH
      (Measure.map ((↑) : NNReal → ℝ) μSub) T hμSubMapFinite
  have hPolarizedLim :
      Tendsto
        (fun n ↦
          signedLebesgueStieltjesIntegralUpTo
            (dyadicPrefixStaircase H T n)
            covariationMeasure
            T)
        atTop
        (nhds
          ((1 / 4 : ℝ) *
            ((∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
                ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
              ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
                ∂(Measure.map ((↑) : NNReal → ℝ) μSub)))) := by
    have hMap :
        Tendsto
          (fun n ↦
            (1 / 4 : ℝ) *
              ((∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
                  ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
                ∫ s in Set.Icc (0 : ℝ) T, dyadicPrefixStaircase H T n s
                  ∂(Measure.map ((↑) : NNReal → ℝ) μSub)))
          atTop
          (nhds
            ((1 / 4 : ℝ) *
              ((∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
                  ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
                ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
                  ∂(Measure.map ((↑) : NNReal → ℝ) μSub)))) := by
      simpa using (hAddLim.sub hSubLim).const_mul (1 / 4 : ℝ)
    refine hMap.congr' ?_
    filter_upwards with n
    exact (dyadicPrefixStaircase_polarizedDifference
      H covariationMeasure hcovariationMeasure hμAddMass hμSubMass
      hμAddFinite hμSubFinite T n).symm
  have hPolarizedEq :
      signedLebesgueStieltjesIntegralUpTo
          (fun s ↦ H s.toNNReal)
          covariationMeasure
          T =
        (1 / 4 : ℝ) *
          ((∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
              ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
            ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
              ∂(Measure.map ((↑) : NNReal → ℝ) μSub)) :=
    tendsto_nhds_unique hSignedLim hPolarizedLim
  have hMapAddIntegral :
      ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μAdd) =
        ∫ s in Set.Icc 0 T, H s ∂μAdd := by
    calc
      ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)
          =
        ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) s
          ∂(Measure.map ((↑) : NNReal → ℝ) μAdd) := by
            rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      _ =
        ∫ s : NNReal,
          Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) (s : ℝ) ∂μAdd := by
            rw [NNReal.isClosedEmbedding_coe.integral_map]
      _ = ∫ s : NNReal, Set.indicator (Set.Icc 0 T) H s ∂μAdd := by
            refine integral_congr_ae ?_
            filter_upwards with s
            by_cases hsT : s ≤ T
            · simp [Set.indicator, hsT]
            · simp [Set.indicator, hsT]
      _ = ∫ s in Set.Icc 0 T, H s ∂μAdd := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
  have hMapSubIntegral :
      ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μSub) =
        ∫ s in Set.Icc 0 T, H s ∂μSub := by
    calc
      ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal ∂(Measure.map ((↑) : NNReal → ℝ) μSub)
          =
        ∫ s : ℝ, Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) s
          ∂(Measure.map ((↑) : NNReal → ℝ) μSub) := by
            rw [← MeasureTheory.integral_indicator measurableSet_Icc]
      _ =
        ∫ s : NNReal,
          Set.indicator (Set.Icc (0 : ℝ) T) (fun s ↦ H s.toNNReal) (s : ℝ) ∂μSub := by
            rw [NNReal.isClosedEmbedding_coe.integral_map]
      _ = ∫ s : NNReal, Set.indicator (Set.Icc 0 T) H s ∂μSub := by
            refine integral_congr_ae ?_
            filter_upwards with s
            by_cases hsT : s ≤ T
            · simp [Set.indicator, hsT]
            · simp [Set.indicator, hsT]
      _ = ∫ s in Set.Icc 0 T, H s ∂μSub := by
            rw [MeasureTheory.integral_indicator measurableSet_Icc]
  -- Proof comment: the levelwise polarized identity pins down the signed limit on the real line,
  -- and the final `integral_map` rewrite transports that limit back to the original `NNReal`
  -- interval integrals.
  calc
    signedLebesgueStieltjesIntegralUpTo
        (fun s ↦ H s.toNNReal)
        covariationMeasure
        T =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
            ∂(Measure.map ((↑) : NNReal → ℝ) μAdd)) -
          ∫ s in Set.Icc (0 : ℝ) T, H s.toNNReal
            ∂(Measure.map ((↑) : NNReal → ℝ) μSub)) := hPolarizedEq
    _ =
      (1 / 4 : ℝ) *
        ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
          ∫ s in Set.Icc 0 T, H s ∂μSub) := by
            rw [hMapAddIntegral, hMapSubIntegral]

/-- Helper for Theorem 25.30: a continuous weight together with continuous self- and mixed
quadratic-covariation witnesses identifies the weighted dyadic mixed sums with the corresponding
signed Lebesgue--Stieltjes integral. -/
theorem
    tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_eq_signedLebesgueStieltjesIntegral
    (H : NNReal → ℝ) {Y Z covYY covZZ covYZ : PathSpace}
    (hYY : HasQuadraticCovariationAlong Y Y covYY)
    (hZZ : HasQuadraticCovariationAlong Z Z covZZ)
    (hYZ : HasQuadraticCovariationAlong Y Z covYZ)
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        covYZ T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    (T : NNReal) :
    Tendsto
      (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
      atTop
      (nhds
        (signedLebesgueStieltjesIntegralUpTo
          (fun s ↦ H s.toNNReal)
          covariationMeasure
          T)) := by
  let covAdd : PathSpace := covYY + (2 : ℝ) • covYZ + covZZ
  let covSub : PathSpace := covYY - (2 : ℝ) • covYZ + covZZ
  have hSqYY : HasSquareVariationAlong Y covYY :=
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self hYY
  have hSqZZ : HasSquareVariationAlong Z covZZ :=
    hasSquareVariationAlong_of_hasQuadraticCovariationAlong_self hZZ
  have hAdd : HasSquareVariationAlong (Y + Z) covAdd := by
    -- Proof comment: the plus path carries the canonical polarized square-variation witness.
    simpa [covAdd] using
      hasSquareVariationAlong_add_of_hasQuadraticCovariationAlong hSqYY hSqZZ hYZ
  have hSub : HasSquareVariationAlong (Y - Z) covSub := by
    -- Proof comment: the minus path is handled by the corresponding subtraction witness.
    simpa [covSub] using
      hasSquareVariationAlong_sub_of_hasQuadraticCovariationAlong hSqYY hSqZZ hYZ
  let μAdd : Measure NNReal := squareVariationStieltjesMeasure hAdd
  let μSub : Measure NNReal := squareVariationStieltjesMeasure hSub
  have hHNN : Continuous H := by
    -- Proof comment: the assumed continuous real extension restricts back to a continuous
    -- `NNReal`-weight.
    convert hH.comp NNReal.continuous_coe using 1
    ext s
    simp
  have hAddLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y + Z) T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, H s ∂μAdd)) := by
    simpa [μAdd] using tendsto_weightedDyadicSquareVariationSum_of_continuous H hHNN hAdd T
  have hSubLim :
      Tendsto
        (fun n ↦ weightedDyadicSquareVariationSum H (Y - Z) T n)
        atTop
        (nhds (∫ s in Set.Icc 0 T, H s ∂μSub)) := by
    simpa [μSub] using tendsto_weightedDyadicSquareVariationSum_of_continuous H hHNN hSub T
  have hPolarized :
      Tendsto
        (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
        atTop
        (nhds
          ((1 / 4 : ℝ) *
            ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
              ∫ s in Set.Icc 0 T, H s ∂μSub))) := by
    have hMap :
        Tendsto
          (fun n ↦
            (1 / 4 : ℝ) *
              (weightedDyadicSquareVariationSum H (Y + Z) T n -
                weightedDyadicSquareVariationSum H (Y - Z) T n))
          atTop
          (nhds
            ((1 / 4 : ℝ) *
              ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
                ∫ s in Set.Icc 0 T, H s ∂μSub))) := by
      simpa using (hAddLim.sub hSubLim).const_mul (1 / 4 : ℝ)
    refine hMap.congr' ?_
    filter_upwards with n
    exact (dyadicQuadraticCovariationIntegralApproximationUpTo_eq_weightedPolarization
      H Y Z T n).symm
  have hTarget :
      signedLebesgueStieltjesIntegralUpTo
          (fun s ↦ H s.toNNReal)
          covariationMeasure
          T =
        (1 / 4 : ℝ) *
          ((∫ s in Set.Icc 0 T, H s ∂μAdd) -
            ∫ s in Set.Icc 0 T, H s ∂μSub) := by
    refine signedLebesgueStieltjesIntegralUpTo_eq_polarizedDifference
      (covYY := covYY) (covZZ := covZZ) (covYZ := covYZ)
      H covariationMeasure hcovariationMeasure ?_ ?_ ?_ ?_ hH T
    · intro t
      simpa [μAdd, covAdd] using (dyadicSquareVariationMeasure_real_Icc_eq hAdd t).symm
    · intro t
      simpa [μSub, covSub] using (dyadicSquareVariationMeasure_real_Icc_eq hSub t).symm
    · intro t
      simpa [μAdd] using squareVariationStieltjesMeasure_Icc_lt_top hAdd t
    · intro t
      simpa [μSub] using squareVariationStieltjesMeasure_Icc_lt_top hSub t
  -- Proof comment: both the dyadic polarization limit and the signed-measure polarization formula
  -- identify the same target quantity, so the desired convergence is just a final rewrite.
  simpa [hTarget] using hPolarized

-- Proof sketch: the dyadic mixed-increment integral against a quadratic covariation path agrees
-- with the corresponding Lebesgue--Stieltjes integral whenever that path is represented by a
-- signed measure.
/-- If a quadratic covariation path `⟨Y, Z⟩` is represented by a signed Stieltjes measure and the
weight is continuous on `ℝ`, then the canonical pathwise integral against `d⟨Y, Z⟩` agrees with
the corresponding signed Lebesgue--Stieltjes integral once the self-covariation witnesses are
made explicit. -/
theorem pathwiseQuadraticCovariationIntegral_eq_lebesgueStieltjesIntegral
    (H : NNReal → ℝ) {Y Z covYY covZZ covYZ : PathSpace}
    (hYY : HasQuadraticCovariationAlong Y Y covYY)
    (hZZ : HasQuadraticCovariationAlong Z Z covZZ)
    (hYZ : HasQuadraticCovariationAlong Y Z covYZ)
    (covariationMeasure : SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ T : NNReal,
        covYZ T =
          signedLebesgueStieltjesIntegralUpTo (fun _ ↦ (1 : ℝ)) covariationMeasure T)
    (hH : Continuous fun s : ℝ ↦ H s.toNNReal)
    :
    pathwiseQuadraticCovariationIntegral H Y Z =
      fun T ↦
        signedLebesgueStieltjesIntegralUpTo
          (fun s ↦ H s.toNNReal)
          covariationMeasure
          T := by
  ext T
  -- Route correction: reduce the canonical integral to the strengthened mixed-sum limit proved
  -- just above, which now takes the self-covariation owners explicitly.
  have hlim :
      Tendsto
        (fun n ↦ dyadicQuadraticCovariationIntegralApproximationUpTo H Y Z T n)
        atTop
        (nhds
          (signedLebesgueStieltjesIntegralUpTo
            (fun s ↦ H s.toNNReal)
            covariationMeasure
            T)) :=
    tendsto_dyadicQuadraticCovariationIntegralApproximationUpTo_eq_signedLebesgueStieltjesIntegral
      H hYY hZZ hYZ covariationMeasure hcovariationMeasure hH T
  exact
    pathwiseQuadraticCovariationIntegral_eq_of_tendsto H Y Z T hlim

-- Proof sketch: rewrite each pairwise pathwise quadratic-covariation integral using the supplied
-- signed-measure realization of the corresponding covariation path and sum over all coordinates.
/-- If the pairwise quadratic covariation paths are represented by signed Stieltjes measures and
the Hessian-entry weights are continuous on `ℝ`, then the quadratic correction term of Theorem
25.30 agrees with the corresponding sum of signed Lebesgue--Stieltjes integrals. -/
theorem pathwiseMultidimensionalItoCorrection_eq_sum_lebesgueStieltjesIntegral
    (F : State → ℝ)
    (X : VectorPathSpace d)
    (cov : Fin d → Fin d → PathSpace)
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (cov i j))
    (covariationMeasure : Fin d → Fin d → SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ i j : Fin d, ∀ T : NNReal,
        cov i j T =
          signedLebesgueStieltjesIntegralUpTo
            (fun _ ↦ (1 : ℝ))
            (covariationMeasure i j)
            T)
    (hWeight :
      ∀ i j : Fin d,
        Continuous fun s : ℝ ↦ (∂²[i, j] F) (X s.toNNReal))
    :
    pathwiseMultidimensionalItoCorrection F X =
      fun T ↦
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
  ext T
  rw [pathwiseMultidimensionalItoCorrection_def]
  -- Proof comment: rewrite each pairwise canonical quadratic-covariation integral by the signed
  -- Lebesgue-Stieltjes formula and then reassemble the finite double sum coordinatewise.
  congr 1
  refine Finset.sum_congr rfl ?_
  intro i hi
  refine Finset.sum_congr rfl ?_
  intro j hj
  simpa using
    congrArg
      (fun integral : PathwiseProcess ↦ integral T)
      (pathwiseQuadraticCovariationIntegral_eq_lebesgueStieltjesIntegral
      (Y := vectorPathComponent X i)
      (Z := vectorPathComponent X j)
      (covYY := cov i i)
      (covZZ := cov j j)
      (covYZ := cov i j)
      (H := fun s ↦ (∂²[i, j] F) (X s))
      (hYY := hcov i i)
      (hZZ := hcov j j)
      (hYZ := hcov i j)
      (covariationMeasure := covariationMeasure i j)
      (hcovariationMeasure := hcovariationMeasure i j)
      (hH := hWeight i j))

-- Proof sketch: this is exactly
-- `pathwiseMultidimensionalItoFormula_eq_canonicalCorrection` with the named correction expanded.
/-- Theorem 25.30: if `X ∈ 𝒞_qv^d` and `F ∈ C²(ℝ^d)`, then
`F (X_T) - F (X_0) = ∫_0^T ∇ F(X_s) dX_s +
  (1 / 2) ∑_{i,j} ∫_0^T ∂ᵢ∂ⱼ F(X_s) d⟨Xⁱ, Xʲ⟩_s`,
where the last term is expressed by the canonical dyadic pathwise quadratic-covariation
integrals. -/
theorem pathwiseMultidimensionalItoFormula
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              pathwiseQuadraticCovariationIntegral
                (fun s ↦ (∂²[i, j] F) (X s))
                (vectorPathComponent X i)
                (vectorPathComponent X j)
                T := by
  simpa [pathwiseMultidimensionalItoCorrection] using
    pathwiseMultidimensionalItoFormula_eq_canonicalCorrection F hf X hX T

/-- If the pairwise quadratic covariation paths are represented by signed Stieltjes measures, then
Theorem 25.30 rewrites to the corresponding sum of signed Lebesgue--Stieltjes integrals. -/
theorem pathwiseMultidimensionalItoFormula_of_covariationMeasureRepresentation
    (F : State → ℝ) (hf : ContDiff ℝ 2 F)
    (X : VectorPathSpace d)
    (hX : X ∈ (𝒞_qv^d))
    (cov : Fin d → Fin d → PathSpace)
    (hcov :
      ∀ i j : Fin d,
        HasQuadraticCovariationAlong
          (vectorPathComponent X i)
          (vectorPathComponent X j)
          (cov i j))
    (covariationMeasure : Fin d → Fin d → SignedMeasure ℝ)
    (hcovariationMeasure :
      ∀ i j : Fin d, ∀ T : NNReal,
        cov i j T =
          signedLebesgueStieltjesIntegralUpTo
            (fun _ ↦ (1 : ℝ))
            (covariationMeasure i j)
            T)
    (hWeight :
      ∀ i j : Fin d,
        Continuous fun s : ℝ ↦ (∂²[i, j] F) (X s.toNNReal))
    (T : NNReal) :
    F (X T) - F (X 0) =
      pathwiseMultidimensionalItoIntegral F X T +
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
  have hcorr :
      pathwiseMultidimensionalItoCorrection F X T =
        (1 / 2 : ℝ) *
          ∑ i : Fin d, ∑ j : Fin d,
              signedLebesgueStieltjesIntegralUpTo
                (fun s ↦ (∂²[i, j] F) (X s.toNNReal))
                (covariationMeasure i j)
                T := by
    simpa using
      congrArg
        (fun correction : PathwiseProcess ↦ correction T)
        (pathwiseMultidimensionalItoCorrection_eq_sum_lebesgueStieltjesIntegral
          F X cov hcov covariationMeasure hcovariationMeasure hWeight)
  rw [← hcorr]
  exact pathwiseMultidimensionalItoFormula_eq_canonicalCorrection F hf X hX T
