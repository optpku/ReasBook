/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap03.Definition_3_1

-- Declarations for this item will be appended below by the statement pipeline.

open ProbabilityTheory

/-- The critical geometric offspring distribution, i.e. the geometric law with success
probability `1 / 2`. -/
noncomputable abbrev criticalGeometricOffspringPMF : PMF ℕ :=
  geometricPMF
    (show 0 < (1 / 2 : ℝ) by norm_num)
    (show (1 / 2 : ℝ) ≤ 1 by norm_num)

-- Proof sketch: rewrite the critical geometric pgf as the geometric series with ratio `s / 2`,
-- identify it with the fractional linear map `s ↦ 1 / (2 - s)` on `[0, 1]`, and then iterate
-- that closed form directly by induction.
/-- Helper for Lemma 21.44: on `[0, 1]`, the critical geometric offspring pgf is the fractional
linear map `s ↦ 1 / (2 - s)`. -/
lemma criticalGeometricOffspringPgf_eq_fractionalLinear {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    probabilityGeneratingFunctionReal criticalGeometricOffspringPMF s = 1 / (2 - s) := by
  have hs_div_two_nonneg : 0 ≤ s / 2 := by
    nlinarith [hs.1]
  have hs_div_two_lt_one : s / 2 < 1 := by
    nlinarith [hs.2]
  have hratio : |s / 2| < 1 := by
    simpa [abs_of_nonneg hs_div_two_nonneg] using hs_div_two_lt_one
  have hs_ne : s ≠ 2 := by
    nlinarith [hs.2]
  rw [probabilityGeneratingFunctionReal_apply]
  calc
    ∑' n : ℕ, (criticalGeometricOffspringPMF n).toReal * s ^ n
      = ∑' n : ℕ, (1 / 2 : ℝ) * ((s / 2) ^ n) := by
          refine tsum_congr fun n ↦ ?_
          -- Proof comment: the pmf mass is `((1 / 2)^n) * (1 / 2)`, and the powers combine into
          -- the stable ratio `(s / 2)^n`.
          have hmass :
              (criticalGeometricOffspringPMF n).toReal = ((1 / 2 : ℝ) ^ n) * (1 / 2) := by
            rw [criticalGeometricOffspringPMF, geometricPMF]
            change (ENNReal.ofReal (geometricPMFReal (1 / 2 : ℝ) n)).toReal =
              ((1 / 2 : ℝ) ^ n) * (1 / 2)
            rw [ENNReal.toReal_ofReal]
            · have hhalf : (1 - (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
                norm_num
              rw [geometricPMFReal, hhalf]
            · exact geometricPMFReal_nonneg (show 0 < (1 / 2 : ℝ) by norm_num)
                (show (1 / 2 : ℝ) ≤ 1 by norm_num)
          rw [hmass]
          have hpow : ((1 / 2 : ℝ) ^ n) * s ^ n = (s / 2) ^ n := by
            rw [← mul_pow]
            ring_nf
          calc
            (((1 / 2 : ℝ) ^ n) * (1 / 2)) * s ^ n =
                (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ n) * s ^ n) := by
                  ring
            _ = (1 / 2 : ℝ) * (s / 2) ^ n := by rw [hpow]
    _ = (1 / 2 : ℝ) * ∑' n : ℕ, (s / 2) ^ n := by rw [tsum_mul_left]
    _ = (1 / 2 : ℝ) * (1 - s / 2)⁻¹ := by
          rw [(hasSum_geometric_of_abs_lt_one hratio).tsum_eq]
    _ = 1 / (2 - s) := by
          field_simp [hs_ne]

/-- Helper for Lemma 21.44: every iterate of the critical geometric offspring pgf maps `[0, 1]`
into itself. -/
lemma criticalGeometricOffspringPgf_iterate_mem_unitInterval (n : ℕ) {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) s ∈
      Set.Icc (0 : ℝ) 1 := by
  induction n generalizing s with
  | zero =>
      -- Proof comment: the zeroth iterate is the identity map, so the interval condition is
      -- unchanged.
      simpa using hs
  | succ n ih =>
      -- Proof comment: apply the pgf once more to the previous iterate, which stays in `[0, 1]`.
      simpa [Function.iterate_succ_apply'] using
        probabilityGeneratingFunctionReal_mem_unitInterval criticalGeometricOffspringPMF
          ⟨_, ih hs⟩

/-- Helper for Lemma 21.44: the Möbius denominator `n + 1 - n s` stays positive on `[0, 1]`. -/
lemma criticalGeometricFractionalLinear_denominator_pos {n : ℕ} {s : ℝ}
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    0 < (n + 1 : ℝ) - n * s := by
  -- Proof comment: `n + 1 - n s = 1 + n * (1 - s)`, and both factors are nonnegative on `[0, 1]`.
  have hn_nonneg : (0 : ℝ) ≤ n := by
    exact_mod_cast Nat.zero_le n
  nlinarith [hs.2, hn_nonneg]

/-- Helper for Lemma 21.44: the positive iterates of the critical geometric offspring pgf satisfy
the announced fractional-linear formula. -/
lemma criticalGeometricOffspringPgf_iterate_succ_eq (m : ℕ) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[m + 1]) s =
      ((((m + 1 : ℕ) : ℝ) - m * s) / (m + 2 - (m + 1) * s)) := by
  induction m generalizing s with
  | zero =>
      -- Proof comment: the first positive iterate is the pgf itself, so the geometric-series
      -- computation gives the claimed formula directly.
      simpa [Function.iterate_one] using criticalGeometricOffspringPgf_eq_fractionalLinear hs
  | succ m ih =>
      -- Route correction: iterate the already-identified fractional linear map directly instead
      -- of introducing the source-side matrix encoding.
      have hih := ih s hs
      let z : ℝ :=
        ((((m + 1 : ℕ) : ℝ) - m * s) / (m + 2 - (m + 1) * s))
      have hz :
          z ∈ Set.Icc (0 : ℝ) 1 := by
        have hIterate :
            ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[m + 1]) s ∈
              Set.Icc (0 : ℝ) 1 :=
          criticalGeometricOffspringPgf_iterate_mem_unitInterval (m + 1) hs
        rw [hih] at hIterate
        simpa [z] using hIterate
      have hdenBase :
          0 < (((m + 1 : ℕ) : ℝ) + 1) - (((m + 1 : ℕ) : ℝ)) * s :=
        criticalGeometricFractionalLinear_denominator_pos (n := m + 1) hs
      have hden :
          0 < (m + 2 : ℝ) - (m + 1) * s := by
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hdenBase ⊢
        exact hdenBase
      have hnextDenBase :
          0 < (((m + 2 : ℕ) : ℝ) + 1) - (((m + 2 : ℕ) : ℝ)) * s :=
        criticalGeometricFractionalLinear_denominator_pos (n := m + 2) hs
      have hnextDen :
          0 < (m + 3 : ℝ) - (m + 2) * s := by
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hnextDenBase ⊢
        exact hnextDenBase
      -- Proof comment: rewrite one more iterate through the closed pgf formula, substitute the
      -- inductive fractional-linear expression, and simplify the resulting rational identity.
      rw [Nat.add_assoc, Function.iterate_succ_apply']
      rw [hih]
      rw [criticalGeometricOffspringPgf_eq_fractionalLinear hz]
      dsimp [z]
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
      field_simp [ne_of_gt hden, ne_of_gt hnextDen]
      ring

/-- Lemma 21.44: For the critical geometric offspring distribution, whose probability generating
function is `probabilityGeneratingFunctionReal criticalGeometricOffspringPMF`, equivalently
`ψ(s) = 1 / (2 - s)`, the `n`th iterate satisfies
`ψ^[n] (s) = (n - (n - 1) s) / (n + 1 - n s)` for every positive `n` and every `s ∈ [0,1]`. -/
theorem critical_geometric_offspring_pgf_iterate_eq (n : ℕ) (hn : 1 ≤ n) (s : ℝ)
    (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ((probabilityGeneratingFunctionReal criticalGeometricOffspringPMF)^[n]) s =
      (((n : ℝ) - (n - 1) * s) / (n + 1 - n * s)) := by
  have hn_pos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn_pos) with ⟨m, rfl⟩
  have hmain := criticalGeometricOffspringPgf_iterate_succ_eq m s hs
  -- Proof comment: after writing the positive index as `m + 1`, the iterate formula is exactly
  -- the dedicated positive-iterate helper.
  norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] at hmain ⊢
  exact hmain
