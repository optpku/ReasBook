/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal Topology

noncomputable section

local notation "PathSpace" => C(NNReal, ℝ)
local notation "PathwiseProcess" => NNReal → ℝ

variable {P : ℕ → ℕ → NNReal}

/-- The `n`-th partition sum defining the `p`-variation of a path on `[0, T]` along the
admissible partition sequence `P`. -/
noncomputable def partitionPVariationSum
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (p : ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    Real.rpow
      (|G (partitionNextPointUpTo P n k T) - G (P n k)|)
      p

/-- The `n`-th partition sum defining quadratic covariation on `[0, T]` along the admissible
partition sequence `P`. -/
noncomputable def partitionQuadraticCovariationSum
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  Finset.sum (Finset.range (partitionBoundIndex P n T)) fun k ↦
    (F (partitionNextPointUpTo P n k T) - F (P n k)) *
      (G (partitionNextPointUpTo P n k T) - G (P n k))

/-- Definition 21.58 (1): `V` is a `p`-variation process for `G` along the admissible partition
sequence `P` when the partition sums converge pointwise to `V`. -/
def HasPVariationAlongPartition
    (p : ℝ) (G : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (V : PathwiseProcess) : Prop :=
  ∀ T : NNReal, Tendsto (partitionPVariationSum P p G T) atTop (nhds (V T))

namespace HasPVariationAlongPartition

/-- A `p`-variation process along `P` carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {p : ℝ} {G : PathSpace} {V : PathwiseProcess}
    (hV : HasPVariationAlongPartition p G P V) (T : NNReal) :
    Tendsto (partitionPVariationSum P p G T) atTop (nhds (V T)) :=
  hV T

end HasPVariationAlongPartition

/-- Definition 21.58 (2): `V` is the square variation `⟨G⟩` along `P` when it is the
`2`-variation process of `G` along `P`. -/
abbrev HasSquareVariationAlongPartition
    (G : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (V : PathwiseProcess) : Prop :=
  HasPVariationAlongPartition 2 G P V

namespace HasSquareVariationAlongPartition

/-- A square-variation process along `P` carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {G : PathSpace} {V : PathwiseProcess}
    (hV : HasSquareVariationAlongPartition G P V) (T : NNReal) :
    Tendsto (partitionPVariationSum P 2 G T) atTop (nhds (V T)) :=
  hV T

end HasSquareVariationAlongPartition

/-- A continuous path has continuous square variation along `P` if it admits a continuous
square-variation path along `P`. -/
def HasContinuousSquareVariationAlongPartition
    (G : PathSpace) (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] : Prop :=
  ∃ V : PathSpace, HasSquareVariationAlongPartition G P V

/-- Definition 21.58 (3): the class `𝒞_qv^P` consists of continuous paths whose square variation
along `P` is represented by a continuous path. -/
def 𝒞_qvAlong
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] : Set PathSpace :=
  fun G ↦ HasContinuousSquareVariationAlongPartition G P

/- Membership in `𝒞_qvAlong P` is the derived set-level view of the owner property
`HasContinuousSquareVariationAlongPartition`. -/
theorem mem_𝒞_qvAlong_iff
    [IsAdmissiblePartitionSequence P] (G : PathSpace) :
    G ∈ 𝒞_qvAlong P ↔ HasContinuousSquareVariationAlongPartition G P :=
  Iff.rfl

/-- Definition 21.58 (4): `covFG` is a quadratic covariation process for `F` and `G` along the
admissible partition sequence `P` when the mixed partition sums converge pointwise to `covFG`. -/
def HasQuadraticCovariationAlongPartition
    (F G : PathSpace) (P : ℕ → ℕ → NNReal)
    [IsAdmissiblePartitionSequence P] (covFG : PathwiseProcess) : Prop :=
  ∀ T : NNReal, Tendsto (partitionQuadraticCovariationSum P F G T) atTop (nhds (covFG T))

namespace HasQuadraticCovariationAlongPartition

/-- A quadratic covariation process along `P` carries the defining mixed-sum convergence at each
fixed time. -/
theorem tendsto_partition_sum
    [IsAdmissiblePartitionSequence P] {F G : PathSpace} {covFG : PathwiseProcess}
    (hcovFG : HasQuadraticCovariationAlongPartition F G P covFG) (T : NNReal) :
    Tendsto (partitionQuadraticCovariationSum P F G T) atTop (nhds (covFG T)) :=
  hcovFG T

end HasQuadraticCovariationAlongPartition

-- A file-local dyadic partition sequence keeps the Chapter 21 dyadic API available even when the
-- earlier example file is still under repair.
namespace Definition2158

/-- Helper for Definition 21.58: the dyadic partition sequence on `[0, ∞)`, whose `n`-th row
consists of the times `k 2^{-n}`. -/
def dyadicPartitionSequence (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

/-- Helper for Definition 21.58: successive points in the `n`-th dyadic row are separated by the
constant gap `((2 : ℝ≥0∞)⁻¹)^n`. -/
lemma dyadicPartitionSequence_succGap (n k : ℕ) :
    edist (dyadicPartitionSequence n k) (dyadicPartitionSequence n (k + 1)) =
      (((2 : ℝ≥0∞)⁻¹) ^ n) := by
  have hpow : (2 : NNReal) ^ n ≠ 0 := by
    positivity
  have hle : dyadicPartitionSequence n k ≤ dyadicPartitionSequence n (k + 1) := by
    -- The dyadic row is increasing because the denominator is fixed and positive.
    rw [dyadicPartitionSequence, dyadicPartitionSequence]
    exact (div_le_div_iff_of_pos_right (show 0 < (2 : NNReal) ^ n by positivity)).2 <| by
      exact_mod_cast Nat.le_succ k
  rw [edist_nndist, NNReal.nndist_eq, tsub_eq_zero_of_le hle]
  rw [max_eq_right]
  · -- After removing the trivial branch of the max, the remaining difference is `1 / 2^n`.
    calc
      ↑(dyadicPartitionSequence n (k + 1) - dyadicPartitionSequence n k : NNReal)
          = ↑(((((k : NNReal) + 1) / (2 : NNReal) ^ n) - ((k : NNReal) / (2 : NNReal) ^ n)) :
              NNReal) := by
                simp [dyadicPartitionSequence, Nat.cast_add]
      _ = ↑((((k : NNReal) / (2 : NNReal) ^ n) + (1 / (2 : NNReal) ^ n) -
            ((k : NNReal) / (2 : NNReal) ^ n)) : NNReal) := by
                rw [add_div]
      _ = ↑((1 / (2 : NNReal) ^ n : NNReal)) := by
                rw [add_tsub_cancel_left]
      _ = (1 : ℝ≥0∞) / (2 : ℝ≥0∞) ^ n := by
                rw [ENNReal.coe_div hpow, ENNReal.coe_one, ENNReal.coe_pow]
                norm_num
      _ = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
                simp [div_eq_mul_inv]
      _ = (((2 : ℝ≥0∞)⁻¹) ^ n) := by
                simpa using (ENNReal.inv_pow (a := (2 : ℝ≥0∞)) (n := n))
  · positivity

/-- Helper for Definition 21.58: the mesh of the `n`-th dyadic partition is its common gap size. -/
lemma partitionMesh_dyadicPartitionSequence (n : ℕ) :
    partitionMesh dyadicPartitionSequence n = (((2 : ℝ≥0∞)⁻¹) ^ n) := by
  -- Every term in the defining supremum is the same dyadic gap.
  rw [partitionMesh]
  simp only [dyadicPartitionSequence_succGap, iSup_const]

/-- Helper for Definition 21.58: the dyadic mesh decays geometrically to `0` in `ℝ≥0∞`. -/
lemma tendsto_partitionMesh_dyadicPartitionSequence :
    Tendsto (fun n : ℕ ↦ partitionMesh dyadicPartitionSequence n) atTop (nhds 0) := by
  -- Rewrite the mesh in closed form and apply the standard ENNReal geometric limit theorem.
  have hlt : ((2 : ℝ≥0∞)⁻¹) < 1 := by
    simp
  simpa [partitionMesh_dyadicPartitionSequence] using
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0∞)⁻¹) hlt)

/-- Helper for Definition 21.58: the file-local dyadic partitions form an admissible partition
sequence. -/
theorem dyadicPartitionSequence_isAdmissible :
    IsAdmissiblePartitionSequence dyadicPartitionSequence := by
  refine
    { zero_eq := ?_
      strictMono := ?_
      nested := ?_
      tendsto_atTop := ?_
      mesh_tendsto_zero := tendsto_partitionMesh_dyadicPartitionSequence }
  · intro n
    simp [dyadicPartitionSequence]
  · intro n
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    have hpow : 0 < (2 : NNReal) ^ n := by
      positivity
    have hk : (k : NNReal) < ((k + 1 : ℕ) : NNReal) := by
      exact_mod_cast Nat.lt_succ_self k
    rw [dyadicPartitionSequence, dyadicPartitionSequence]
    exact (div_lt_div_iff_of_pos_right hpow).2 hk
  · intro n t ht
    rcases (Set.mem_range.mp <| by simpa [partitionPointSet] using ht) with ⟨k, rfl⟩
    change dyadicPartitionSequence n k ∈ Set.range (dyadicPartitionSequence (n + 1))
    refine ⟨2 * k, ?_⟩
    simp [dyadicPartitionSequence, pow_succ, mul_assoc, mul_comm, div_eq_mul_inv]
  · intro n
    simpa [dyadicPartitionSequence, div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop.atTop_mul_const
        (show 0 < ((2 : NNReal) ^ n)⁻¹ by positivity))

/-- Helper for Definition 21.58: the file-local dyadic partition sequence carries the expected
admissible-partition instance. -/
instance instIsAdmissiblePartitionSequenceDyadicPartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence :=
  dyadicPartitionSequence_isAdmissible

end Definition2158

/-- The `n`-th dyadic partition sum used to define the `p`-variation of a path on `[0, T]`. -/
noncomputable abbrev dyadic_p_variation_sum
    (p : ℝ) (G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  partitionPVariationSum Definition2158.dyadicPartitionSequence p G T n

/-- The `n`-th dyadic partition sum used to define quadratic covariation on `[0, T]`. -/
noncomputable abbrev dyadic_quadratic_covariation_sum
    (F G : PathSpace) (T : NNReal) (n : ℕ) : ℝ :=
  partitionQuadraticCovariationSum Definition2158.dyadicPartitionSequence F G T n

/-- The dyadic specialization of Definition 21.58 (1). -/
abbrev HasPVariationAlong (p : ℝ) (G : PathSpace) (V : PathwiseProcess) : Prop :=
  HasPVariationAlongPartition p G Definition2158.dyadicPartitionSequence V

namespace HasPVariationAlong

/-- A dyadic `p`-variation process carries the defining convergence at each fixed time. -/
theorem tendsto_partition_sum
    {p : ℝ} {G : PathSpace} {V : PathwiseProcess} (hV : HasPVariationAlong p G V) (T : NNReal) :
    Tendsto (dyadic_p_variation_sum p G T) atTop (nhds (V T)) :=
  hV T

end HasPVariationAlong

/-- The dyadic specialization of Definition 21.58 (2). -/
abbrev HasSquareVariationAlong (G : PathSpace) (V : PathwiseProcess) : Prop :=
  HasSquareVariationAlongPartition G Definition2158.dyadicPartitionSequence V

/-- A continuous path has continuous square variation along the dyadic partitions if it admits a
continuous square-variation path. -/
abbrev HasContinuousSquareVariation (G : PathSpace) : Prop :=
  HasContinuousSquareVariationAlongPartition G Definition2158.dyadicPartitionSequence

/-- Definition 21.58 (3): the class `𝒞_qv` consists of continuous paths whose square variation
process is continuous in time along the dyadic partitions. -/
abbrev 𝒞_qv : Set PathSpace :=
  𝒞_qvAlong Definition2158.dyadicPartitionSequence

/- Membership in `𝒞_qv` is the derived set-level view of the owner property
`HasContinuousSquareVariation`. -/
theorem mem_𝒞_qv_iff (G : PathSpace) :
    G ∈ 𝒞_qv ↔ HasContinuousSquareVariation G :=
  Iff.rfl

/-- The dyadic specialization of Definition 21.58 (4). -/
abbrev HasQuadraticCovariationAlong
    (F G : PathSpace) (covFG : PathwiseProcess) : Prop :=
  HasQuadraticCovariationAlongPartition F G Definition2158.dyadicPartitionSequence covFG

namespace HasQuadraticCovariationAlong

/-- A dyadic quadratic covariation process carries the defining mixed-sum convergence at each
fixed time. -/
theorem tendsto_partition_sum
    {F G : PathSpace} {covFG : PathwiseProcess}
    (hcovFG : HasQuadraticCovariationAlong F G covFG) (T : NNReal) :
    Tendsto (dyadic_quadratic_covariation_sum F G T) atTop (nhds (covFG T)) :=
  hcovFG T

end HasQuadraticCovariationAlong

/-- Helper for Definition 21.58: the polarized difference of the squared increments of `a + b`
and `a - b` recovers the mixed product `a * b`. -/
lemma polarizationTermIdentity (a b : ℝ) :
    ((Real.rpow |a + b| 2) - Real.rpow |a - b| 2) / 4 = a * b := by
  -- Normalize the two `Real.rpow` terms to ordinary squares.
  have hadd : Real.rpow |a + b| (2 : ℝ) = (a + b) ^ 2 := by
    rw [← Real.rpow_natCast]
    simpa using (sq_abs (a + b))
  have hsub : Real.rpow |a - b| (2 : ℝ) = (a - b) ^ 2 := by
    rw [← Real.rpow_natCast]
    simpa using (sq_abs (a - b))
  rw [hadd, hsub]
  -- The remaining statement is a polynomial identity after removing the absolute values.
  ring

/-- Helper for Definition 21.58: the mixed partition sum is the polarization difference of the
square-variation sums of `F + G` and `F - G`. -/
lemma partitionQuadraticCovariationSum_eq_polarization
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    (F G : PathSpace) (T : NNReal) (n : ℕ) :
    partitionQuadraticCovariationSum P F G T n =
      ((partitionPVariationSum P 2 (F + G) T n) -
        (partitionPVariationSum P 2 (F - G) T n)) / 4 := by
  let s := Finset.range (partitionBoundIndex P n T)
  let addTerm : ℕ → ℝ := fun k ↦
    Real.rpow
      (|((F + G) (partitionNextPointUpTo P n k T)) - ((F + G) (P n k))|)
      2
  let subTerm : ℕ → ℝ := fun k ↦
    Real.rpow
      (|((F - G) (partitionNextPointUpTo P n k T)) - ((F - G) (P n k))|)
      2
  -- Rewrite each mixed increment by the scalar polarization identity.
  have hterm :
      ∀ k ∈ s,
        (F (partitionNextPointUpTo P n k T) - F (P n k)) *
            (G (partitionNextPointUpTo P n k T) - G (P n k)) =
          (addTerm k - subTerm k) / 4 := by
    intro k hk
    simp only [addTerm, subTerm, ContinuousMap.add_apply, ContinuousMap.sub_apply]
    have hadd :
        (F (partitionNextPointUpTo P n k T) + G (partitionNextPointUpTo P n k T)) -
            (F (P n k) + G (P n k)) =
          (F (partitionNextPointUpTo P n k T) - F (P n k)) +
            (G (partitionNextPointUpTo P n k T) - G (P n k)) := by
      ring
    have hsub :
        (F (partitionNextPointUpTo P n k T) - G (partitionNextPointUpTo P n k T)) -
            (F (P n k) - G (P n k)) =
          (F (partitionNextPointUpTo P n k T) - F (P n k)) -
            (G (partitionNextPointUpTo P n k T) - G (P n k)) := by
      ring
    rw [hadd, hsub, polarizationTermIdentity]
  -- Sum the termwise identity and regroup the finite sums.
  calc
    partitionQuadraticCovariationSum P F G T n
        = Finset.sum s (fun k ↦ (addTerm k - subTerm k) / 4) := by
            unfold partitionQuadraticCovariationSum
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact hterm k (by simpa [s] using hk)
    _ = (Finset.sum s addTerm - Finset.sum s subTerm) / 4 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_mul]
    _ = (partitionPVariationSum P 2 (F + G) T n -
          partitionPVariationSum P 2 (F - G) T n) / 4 := by
      simp only [partitionPVariationSum, s, addTerm, subTerm]

/-- Helper for Definition 21.58: continuous square-variation witnesses for `F - G` and `F + G`
produce a continuous quadratic-covariation witness for `F` and `G`. -/
lemma hasQuadraticCovariationAlongPartition_of_squareVariationWitnesses
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P]
    {F G Vsub Vadd : PathSpace}
    (hVsub : HasSquareVariationAlongPartition (F - G) P Vsub)
    (hVadd : HasSquareVariationAlongPartition (F + G) P Vadd) :
    HasQuadraticCovariationAlongPartition F G P (((1 / 4 : ℝ) • (Vadd - Vsub)) : PathSpace) := by
  intro T
  -- Pass to the limit in the polarized difference of the two square-variation sums.
  have hpolarized :
      Tendsto
        (fun n ↦
          ((partitionPVariationSum P 2 (F + G) T n) -
            (partitionPVariationSum P 2 (F - G) T n)) / 4)
        atTop
        (nhds ((((1 / 4 : ℝ) • (Vadd - Vsub)) : PathSpace) T)) := by
    simpa [ContinuousMap.smul_apply, ContinuousMap.sub_apply, div_eq_mul_inv, smul_eq_mul,
      mul_comm, mul_left_comm, mul_assoc] using
      ((HasSquareVariationAlongPartition.tendsto_partition_sum hVadd T).sub
        (HasSquareVariationAlongPartition.tendsto_partition_sum hVsub T)).mul_const
        ((1 / 4 : ℝ))
  -- Replace the source sequence by the partition-sum polarization formula.
  convert hpolarized using 1
  ext n
  exact partitionQuadraticCovariationSum_eq_polarization P F G T n

-- Proof sketch: choose continuous square-variation realizations of `F + G` and `F - G`, define
-- the mixed bracket by the polarization formula
-- `((⟨F + G⟩ - ⟨F - G⟩) / 4)_T`, and pass to the limit in the partition sums using the
-- termwise polarization identity for mixed increments.
/-- If `F + G` and `F - G` have continuous square variation along the admissible partition
sequence `P`, then the quadratic covariation `⟨F,G⟩` along `P` exists and is represented by a
continuous path. -/
theorem exists_quadratic_covariation_along_partition_of_hasContinuousSquareVariation
    (P : ℕ → ℕ → NNReal) [IsAdmissiblePartitionSequence P] {F G : PathSpace}
    (hFsubG : HasContinuousSquareVariationAlongPartition (F - G) P)
    (hFaddG : HasContinuousSquareVariationAlongPartition (F + G) P) :
    ∃ covFG : PathSpace, HasQuadraticCovariationAlongPartition F G P covFG := by
  rcases hFsubG with ⟨Vsub, hVsub⟩
  rcases hFaddG with ⟨Vadd, hVadd⟩
  -- Use the polarized difference of the two square-variation witnesses as the bracket path.
  refine ⟨((1 / 4 : ℝ) • (Vadd - Vsub)), ?_⟩
  exact hasQuadraticCovariationAlongPartition_of_squareVariationWitnesses P hVsub hVadd

/-- If `F + G` and `F - G` lie in `𝒞_qv`, then the dyadic quadratic covariation `⟨F,G⟩` exists and
is represented by a continuous path. -/
theorem exists_quadratic_covariation_along_of_hasContinuousSquareVariation
    {F G : PathSpace}
    (hFsubG : HasContinuousSquareVariation (F - G))
    (hFaddG : HasContinuousSquareVariation (F + G)) :
    ∃ covFG : PathSpace, HasQuadraticCovariationAlong F G covFG := by
  -- Unfold the dyadic abbreviations once and reuse the partition-level existence result.
  simpa [HasContinuousSquareVariation, HasQuadraticCovariationAlong] using
    exists_quadratic_covariation_along_partition_of_hasContinuousSquareVariation
      Definition2158.dyadicPartitionSequence hFsubG hFaddG
