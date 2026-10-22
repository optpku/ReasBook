/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_56

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped ENNReal Topology

noncomputable section

/-- The dyadic partition sequence on `[0, ∞)`, whose `n`-th row consists of the times
`k 2^{-n}`. -/
def dyadicPartitionSequence (n k : ℕ) : NNReal :=
  (k : NNReal) / (2 : NNReal) ^ n

/-- A nonnegative time belongs to the `n`-th dyadic partition exactly when it is a multiple of the
mesh size `2^{-n}` with a natural-number coefficient. -/
theorem mem_partitionPointSet_dyadicPartitionSequence_iff {n : ℕ} {t : NNReal} :
    t ∈ partitionPointSet dyadicPartitionSequence n ↔
      ∃ k : ℕ, t = (k : NNReal) / (2 : NNReal) ^ n := by
  change t ∈ Set.range (dyadicPartitionSequence n) ↔
    ∃ k : ℕ, t = (k : NNReal) / (2 : NNReal) ^ n
  simp [dyadicPartitionSequence, eq_comm]

/-- Helper for Example 21.57: successive points in the `n`-th dyadic row are separated by the
constant gap `((2 : ℝ≥0∞)⁻¹)^n`. -/
lemma dyadicPartitionSequence_succGap (n k : ℕ) :
    edist (dyadicPartitionSequence n k) (dyadicPartitionSequence n (k + 1)) =
      ((2 : ℝ≥0∞)⁻¹) ^ n := by
  have hpow : (2 : NNReal) ^ n ≠ 0 := by
    positivity
  have hle :
      dyadicPartitionSequence n k ≤ dyadicPartitionSequence n (k + 1) := by
    -- The dyadic row is increasing because the denominator is fixed and positive.
    rw [dyadicPartitionSequence, dyadicPartitionSequence]
    exact (div_le_div_iff_of_pos_right (show 0 < (2 : NNReal) ^ n by positivity)).2 <| by
      exact_mod_cast Nat.le_succ k
  rw [edist_nndist, NNReal.nndist_eq, tsub_eq_zero_of_le hle]
  rw [max_eq_right]
  · -- After removing the trivial branch of the max, the remaining truncated difference
    -- is `1 / 2^n`.
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
              rw [ENNReal.coe_div hpow, ENNReal.coe_one]
              simpa using
                congrArg (fun x : ℝ≥0∞ ↦ (1 : ℝ≥0∞) / x) (ENNReal.coe_pow (2 : NNReal) n)
      _ = ((2 : ℝ≥0∞)⁻¹) ^ n := by
              rw [div_eq_mul_inv, one_mul, ENNReal.inv_pow]
  · positivity

/-- Helper for Example 21.57: the mesh of the `n`-th dyadic partition is the common size of its
successive gaps. -/
lemma partitionMesh_dyadicPartitionSequence (n : ℕ) :
    partitionMesh dyadicPartitionSequence n = ((2 : ℝ≥0∞)⁻¹) ^ n := by
  -- Every term in the defining supremum is the same dyadic gap.
  rw [partitionMesh]
  simp only [dyadicPartitionSequence_succGap, iSup_const]

/-- Helper for Example 21.57: the dyadic mesh decays geometrically to `0` in `ℝ≥0∞`. -/
lemma tendsto_partitionMesh_dyadicPartitionSequence :
    Tendsto (fun n : ℕ ↦ partitionMesh dyadicPartitionSequence n) atTop (𝓝 0) := by
  -- Rewrite the mesh in closed form and apply the standard ENNReal geometric limit theorem.
  have hhalf : ((2 : ℝ≥0∞)⁻¹) < 1 := by
    simp
  simpa [partitionMesh_dyadicPartitionSequence] using
    (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ≥0∞)⁻¹) hhalf)

/-- Helper for Example 21.57: the dyadic partitions define an admissible partition-sequence
instance. -/
instance instIsAdmissiblePartitionSequenceDyadicPartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence where
  zero_eq n := by
    simp [dyadicPartitionSequence]
  strictMono n := by
    refine strictMono_nat_of_lt_succ fun k ↦ ?_
    have hpow : 0 < (2 : NNReal) ^ n := by
      positivity
    have hk : (k : NNReal) < ((k + 1 : ℕ) : NNReal) := by
      exact_mod_cast Nat.lt_succ_self k
    rw [dyadicPartitionSequence, dyadicPartitionSequence]
    exact (div_lt_div_iff_of_pos_right hpow).2 hk
  nested n := by
    intro t ht
    rcases (Set.mem_range.mp <| by simpa [partitionPointSet] using ht) with ⟨k, rfl⟩
    change dyadicPartitionSequence n k ∈ Set.range (dyadicPartitionSequence (n + 1))
    refine ⟨2 * k, ?_⟩
    simp [dyadicPartitionSequence, pow_succ, mul_assoc, mul_comm, div_eq_mul_inv]
  tendsto_atTop n := by
    simpa [dyadicPartitionSequence, div_eq_mul_inv] using
      (tendsto_natCast_atTop_atTop.atTop_mul_const
        (show 0 < ((2 : NNReal) ^ n)⁻¹ by positivity))
  mesh_tendsto_zero := by
    -- The mesh has already been identified with a geometric ENNReal sequence.
    exact tendsto_partitionMesh_dyadicPartitionSequence

/-- Example 21.57: the dyadic partitions form an admissible partition sequence in the sense of
Definition 21.56. -/
theorem dyadicPartitionSequence_isAdmissiblePartitionSequence :
    IsAdmissiblePartitionSequence dyadicPartitionSequence :=
  inferInstance
