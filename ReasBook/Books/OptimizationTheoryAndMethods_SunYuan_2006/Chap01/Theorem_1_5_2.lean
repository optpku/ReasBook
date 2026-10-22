/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Definition_1_5_extra_1
import Mathlib.Analysis.Normed.Group.Continuity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open Filter

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E]

/-- The explicit real sequence used in the textbook counterexample to the converse of
Theorem 1.5.2. -/
def alternatingFactorialCounterexample : ℕ → ℝ
  | 0 => 1
  | n + 1 =>
      let i := n / 2 + 1
      if n % 2 = 0 then 1 / (Nat.factorial i : ℝ) else 2 / (Nat.factorial i : ℝ)

/-- Unfolding formula for `alternatingFactorialCounterexample` on successor indices. -/
theorem alternatingFactorialCounterexample_succ (n : ℕ) :
    alternatingFactorialCounterexample (n + 1) =
      let i := n / 2 + 1
      if n % 2 = 0 then 1 / (Nat.factorial i : ℝ) else 2 / (Nat.factorial i : ℝ) := by
  -- This is just the recursive branch of the definition.
  rfl

/-- Helper for Chapter01 Theorem 1.5.2: the reverse-triangle estimate controls the normalized step
error by the first-order `Q`-error ratio whenever the denominator is nonzero. -/
lemma stepRatio_sub_one_le_qErrorRatio {x : ℕ → E} {xStar : E} {k : ℕ}
    (hk : x k ≠ xStar) :
    |‖x (k + 1) - x k‖ / ‖x k - xStar‖ - 1| ≤ qErrorRatio x xStar 1 k := by
  have hnorm_pos : 0 < ‖x k - xStar‖ := by
    exact norm_pos_iff.2 (sub_ne_zero.mpr hk)
  have htriangle :
      |‖x (k + 1) - x k‖ - ‖x k - xStar‖| ≤ ‖x (k + 1) - xStar‖ := by
    -- Use the reverse triangle inequality on
    -- `(x (k + 1) - x k)` and `-(x k - xStar)`.
    have haux :
        |‖x k - x (k + 1)‖ - ‖x k - xStar‖| ≤
          ‖(x k - x (k + 1)) - (x k - xStar)‖ := by
      exact abs_norm_sub_norm_le (x k - x (k + 1)) (x k - xStar)
    have hnorm :
        ‖(x k - x (k + 1)) - (x k - xStar)‖ = ‖x (k + 1) - xStar‖ := by
      have hvec : (x k - x (k + 1)) - (x k - xStar) = xStar - x (k + 1) := by
        abel_nf
      rw [hvec, norm_sub_rev]
    calc
      |‖x (k + 1) - x k‖ - ‖x k - xStar‖|
        = |‖x k - x (k + 1)‖ - ‖x k - xStar‖| := by
            rw [norm_sub_rev]
      _ ≤ ‖(x k - x (k + 1)) - (x k - xStar)‖ := haux
      _ = ‖x (k + 1) - xStar‖ := hnorm
  calc
    |‖x (k + 1) - x k‖ / ‖x k - xStar‖ - 1|
      = |(‖x (k + 1) - x k‖ - ‖x k - xStar‖) / ‖x k - xStar‖| := by
          rw [show (1 : ℝ) = ‖x k - xStar‖ / ‖x k - xStar‖ by
            rw [div_self hnorm_pos.ne']]
          rw [sub_div]
    _ = |‖x (k + 1) - x k‖ - ‖x k - xStar‖| / ‖x k - xStar‖ := by
          rw [abs_div, abs_of_pos hnorm_pos]
    _ ≤ ‖x (k + 1) - xStar‖ / ‖x k - xStar‖ := by
          exact div_le_div_of_nonneg_right htriangle hnorm_pos.le
    _ = qErrorRatio x xStar 1 k := by
          simp [qErrorRatio, Real.rpow_one]

/-- Helper for Chapter01 Theorem 1.5.2: the counterexample values on each odd-even pair are the
factorial expressions stated in the textbook. -/
lemma alternatingFactorialCounterexample_pair_values (n : ℕ) :
    alternatingFactorialCounterexample (2 * n + 1) =
        1 / (Nat.factorial (n + 1) : ℝ) ∧
      alternatingFactorialCounterexample (2 * n + 2) =
        2 / (Nat.factorial (n + 1) : ℝ) := by
  constructor
  · -- The odd term is the first element of the next factorial pair.
    calc
      alternatingFactorialCounterexample (2 * n + 1)
        = let i := (2 * n) / 2 + 1
            if (2 * n) % 2 = 0 then 1 / (Nat.factorial i : ℝ) else 2 / (Nat.factorial i : ℝ) := by
            simpa using alternatingFactorialCounterexample_succ (2 * n)
      _ = 1 / (Nat.factorial (n + 1) : ℝ) := by
            simp
  · -- The even term is the second element of the same factorial pair.
    calc
      alternatingFactorialCounterexample (2 * n + 2)
        = let i := (2 * n + 1) / 2 + 1
            if (2 * n + 1) % 2 = 0 then
              1 / (Nat.factorial i : ℝ)
            else
              2 / (Nat.factorial i : ℝ) := by
            convert alternatingFactorialCounterexample_succ (2 * n + 1) using 1
      _ = 2 / (Nat.factorial (n + 1) : ℝ) := by
            have hdiv : (2 * n + 1) / 2 = n := by
              omega
            have hmod : (2 * n + 1) % 2 = 1 := by
              omega
            simp [hdiv, hmod]

/-- Helper for Chapter01 Theorem 1.5.2: every normalized step-ratio error in the alternating
factorial counterexample is bounded by the reciprocal tail `1 / (k + 1)`. -/
lemma alternatingFactorialCounterexample_stepRatio_sub_one_le_one_div (k : ℕ) :
    |‖alternatingFactorialCounterexample (k + 1) - alternatingFactorialCounterexample k‖ /
        ‖alternatingFactorialCounterexample k‖ - 1| ≤
      1 / (k + 1 : ℝ) := by
  rcases k with _ | k
  · -- The initial index is a direct computation.
    norm_num [alternatingFactorialCounterexample]
  · rcases Nat.even_or_odd k with hk | hk
    · rcases hk with ⟨n, rfl⟩
      rcases alternatingFactorialCounterexample_pair_values n with ⟨hodd, heven⟩
      have hfac_pos : 0 < (Nat.factorial (n + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (n + 1)
      have hsub :
          (2 / (Nat.factorial (n + 1) : ℝ) : ℝ) - 1 / (Nat.factorial (n + 1) : ℝ) =
            1 / (Nat.factorial (n + 1) : ℝ) := by
        field_simp [hfac_pos.ne']
        ring
      have hone_div_ne : (1 / (Nat.factorial (n + 1) : ℝ) : ℝ) ≠ 0 := by
        positivity
      have hratio :
          ‖alternatingFactorialCounterexample (2 * n + 2) -
              alternatingFactorialCounterexample (2 * n + 1)‖ /
            ‖alternatingFactorialCounterexample (2 * n + 1)‖ =
              1 := by
        -- On odd indices the step is exactly one current error.
        rw [heven, hodd]
        calc
          ‖(2 / (Nat.factorial (n + 1) : ℝ) : ℝ) - 1 / (Nat.factorial (n + 1) : ℝ)‖ /
              ‖(1 / (Nat.factorial (n + 1) : ℝ) : ℝ)‖
            = ‖(1 / (Nat.factorial (n + 1) : ℝ) : ℝ)‖ /
                ‖(1 / (Nat.factorial (n + 1) : ℝ) : ℝ)‖ := by
                  rw [hsub]
          _ = 1 := by
                rw [div_self (norm_ne_zero_iff.2 hone_div_ne)]
      have hratio' :
          ‖alternatingFactorialCounterexample (n + (n + 2)) -
              alternatingFactorialCounterexample (n + (n + 1))‖ /
            ‖alternatingFactorialCounterexample (n + (n + 1))‖ =
              1 := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using hratio
      calc
        |‖alternatingFactorialCounterexample (n + (n + 2)) -
            alternatingFactorialCounterexample (n + (n + 1))‖ /
            ‖alternatingFactorialCounterexample (n + (n + 1))‖ - 1|
          = |(1 : ℝ) - 1| := by
              rw [hratio']
        _ = 0 := by norm_num
        _ ≤ 1 / (↑(n + n + 1) + 1) := by positivity
    · rcases hk with ⟨n, rfl⟩
      rcases alternatingFactorialCounterexample_pair_values n with ⟨_, heven⟩
      rcases alternatingFactorialCounterexample_pair_values (n + 1) with ⟨hoddNext, _⟩
      have hoddNext' :
          alternatingFactorialCounterexample (2 * n + 3) =
            1 / (Nat.factorial (n + 2) : ℝ) := by
        simpa [two_mul, add_assoc, add_left_comm, add_comm] using hoddNext
      have hfac_pos : 0 < (Nat.factorial (n + 1) : ℝ) := by
        exact_mod_cast Nat.factorial_pos (n + 1)
      have hfac_succ :
          (Nat.factorial (n + 2) : ℝ) = (n + 2 : ℝ) * (Nat.factorial (n + 1) : ℝ) := by
        exact_mod_cast (Nat.factorial_succ (n + 1))
      have hmul_pos : 0 < (n + 2 : ℝ) * (Nat.factorial (n + 1) : ℝ) := by
        positivity
      have hratio :
          ‖alternatingFactorialCounterexample (2 * n + 3) -
              alternatingFactorialCounterexample (2 * n + 2)‖ /
            ‖alternatingFactorialCounterexample (2 * n + 2)‖ =
              1 - 1 / (2 * (n + 2 : ℝ)) := by
        -- On even indices the textbook formula gives the explicit defect
        -- `1 / (2 * (n + 2))`.
        rw [hoddNext', heven, hfac_succ]
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        have hneg :
            (1 / ((n + 2 : ℝ) * (Nat.factorial (n + 1) : ℝ)) -
                2 / (Nat.factorial (n + 1) : ℝ) : ℝ) < 0 := by
          have hn2_pos : (0 : ℝ) < (n + 2 : ℝ) := by
            positivity
          field_simp [hfac_pos.ne', hmul_pos.ne']
          nlinarith
        rw [abs_of_neg hneg]
        have hden_nonneg : 0 ≤ (2 / (Nat.factorial (n + 1) : ℝ) : ℝ) := by
          positivity
        rw [abs_of_nonneg hden_nonneg]
        field_simp [hfac_pos.ne', hmul_pos.ne']
        ring
      have htail_pos : 0 < (2 * n + 3 : ℝ) := by
        positivity
      have hbound :
          1 / (2 * (n + 2 : ℝ)) ≤ 1 / (2 * n + 3 : ℝ) := by
        have hden_le : (2 * n + 3 : ℝ) ≤ 2 * (n + 2 : ℝ) := by
          nlinarith
        exact one_div_le_one_div_of_le htail_pos hden_le
      have hbound' :
          1 / (2 * (n + 2 : ℝ)) ≤ 1 / (↑(2 * n + 1 + 1) + 1) := by
        have hbound_simpl :
            (↑n + 2 : ℝ)⁻¹ * 2⁻¹ ≤ (2 * ↑n + 3 : ℝ)⁻¹ := by
          simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hbound
        have hrhs : (2 * ↑n + 3 : ℝ)⁻¹ = (2 * ↑n + 1 + 1 + 1 : ℝ)⁻¹ := by
          ring_nf
        simpa [one_div, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          hbound_simpl.trans_eq hrhs
      have hratio'' :
          ‖alternatingFactorialCounterexample (2 * n + 1 + 1 + 1) -
              alternatingFactorialCounterexample (2 * n + 1 + 1)‖ /
            ‖alternatingFactorialCounterexample (2 * n + 1 + 1)‖ =
              1 - 1 / (2 * (n + 2 : ℝ)) := by
        convert hratio using 1 <;> omega
      calc
        |‖alternatingFactorialCounterexample (2 * n + 1 + 1 + 1) -
            alternatingFactorialCounterexample (2 * n + 1 + 1)‖ /
            ‖alternatingFactorialCounterexample (2 * n + 1 + 1)‖ - 1|
          = |(1 - 1 / (2 * (n + 2 : ℝ)) : ℝ) - 1| := by
              rw [hratio'']
        _ = 1 / (2 * (n + 2 : ℝ)) := by
              have hnonneg : 0 ≤ 1 / (2 * (n + 2 : ℝ)) := by
                positivity
              have hrewrite :
                  (1 - 1 / (2 * (n + 2 : ℝ)) : ℝ) - 1 =
                    -(1 / (2 * (n + 2 : ℝ))) := by
                ring
              rw [hrewrite, abs_neg, abs_of_nonneg hnonneg]
        _ ≤ 1 / (↑(2 * n + 1 + 1) + 1) := hbound'

/-- Helper for Chapter01 Theorem 1.5.2: along the odd subsequence, the counterexample has
constant first-order `Q`-error ratio `2`. -/
lemma alternatingFactorialCounterexample_qErrorRatio_odd (n : ℕ) :
    qErrorRatio alternatingFactorialCounterexample 0 1 (2 * n + 1) = 2 := by
  rcases alternatingFactorialCounterexample_pair_values n with ⟨hodd, heven⟩
  let f : ℝ := Nat.factorial (n + 1)
  have hfac_pos : 0 < (Nat.factorial (n + 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos (n + 1)
  have hnum_nonneg : 0 ≤ (2 / f : ℝ) := by
    positivity
  have hden_nonneg : 0 ≤ (1 / f : ℝ) := by
    positivity
  have hnum_eq : ‖(2 / f : ℝ) - 0‖ = 2 / f := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hnum_nonneg]
  have hden_eq : Real.rpow ‖(1 / f : ℝ) - 0‖ 1 = 1 / f := by
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hden_nonneg]
    simpa using (Real.rpow_one (1 / f : ℝ))
  -- Rewrite the `Q`-ratio at `α = 1` using the explicit odd-even pair formulas.
  calc
    qErrorRatio alternatingFactorialCounterexample 0 1 (2 * n + 1)
      = (2 / f) / (1 / f) := by
          rw [qErrorRatio, heven, hodd, hnum_eq, hden_eq]
    _ = 2 := by
      calc
        (2 / f) / (1 / f) = 2 * (f⁻¹ * f) := by
          simp [div_eq_mul_inv, mul_assoc]
        _ = 2 := by
          rw [inv_mul_cancel₀ hfac_pos.ne', mul_one]

/-- Helper lemma: if a sequence converges `Q`-superlinearly to `xStar`, then the normalized step
lengths `‖x (k + 1) - x k‖ / ‖x k - xStar‖` tend to `1` along the tail where the denominator is
nonzero. -/
theorem hasQSuperlinearConvergenceTo_stepRatio_tendsto_one_restricted {E : Type u}
    [NormedAddCommGroup E] (x : ℕ → E) (xStar : E)
    (hq : HasQSuperlinearConvergenceTo x xStar) :
    Tendsto
      (fun k ↦ ‖x (k + 1) - x k‖ / ‖x k - xStar‖)
      (atTop ⊓ principal {k | x k ≠ xStar})
      (nhds 1) := by
  let l : Filter ℕ := atTop ⊓ principal {k | x k ≠ xStar}
  have hratio_tendsto : Tendsto (qErrorRatio x xStar 1) l (nhds 0) := by
    -- Restrict the known `Q`-ratio limit to the denominator-safe filter.
    exact hq.ratio_tendsto.mono_left inf_le_left
  have hnonzero : ∀ᶠ k in l, x k ≠ xStar := by
    exact mem_inf_of_right (by simp)
  have hbound :
      ∀ᶠ k in l,
        ‖‖x (k + 1) - x k‖ / ‖x k - xStar‖ - 1‖ ≤ qErrorRatio x xStar 1 k := by
    filter_upwards [hnonzero] with k hk
    -- The source proof reduces the step-ratio defect to the `Q`-ratio defect.
    simpa [Real.norm_eq_abs] using
      stepRatio_sub_one_le_qErrorRatio (x := x) (xStar := xStar) (k := k) hk
  have hstep_sub_tendsto :
      Tendsto (fun k ↦ ‖x (k + 1) - x k‖ / ‖x k - xStar‖ - 1) l (nhds 0) := by
    exact squeeze_zero_norm' hbound hratio_tendsto
  -- Add back the constant `1` to recover the step ratio itself.
  simpa [l] using
    hstep_sub_tendsto.add
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) l (nhds 1))

/-- Chapter01 Theorem 1.5.2 (1): if a sequence converges `Q`-superlinearly to `xStar` and the
current errors are nonzero on a tail, then the normalized step lengths
`‖x (k + 1) - x k‖ / ‖x k - xStar‖` tend to `1`. -/
theorem hasQSuperlinearConvergenceTo_stepRatio_tendsto_one {E : Type u}
    [NormedAddCommGroup E] (x : ℕ → E) (xStar : E)
    (hq : HasQSuperlinearConvergenceTo x xStar)
    (hne : ∀ᶠ k in atTop, x k ≠ xStar) :
    Tendsto (fun k ↦ ‖x (k + 1) - x k‖ / ‖x k - xStar‖) atTop (nhds 1) := by
  -- Collapse the restricted filter to `atTop` using the eventual nonvanishing tail.
  simpa [inf_eq_left.2 (by rwa [Filter.le_principal_iff] : atTop ≤ principal {k | x k ≠ xStar})] using
    hasQSuperlinearConvergenceTo_stepRatio_tendsto_one_restricted (x := x) (xStar := xStar) hq

/-- The explicit sequence `alternatingFactorialCounterexample` has normalized step lengths tending
to `1`. -/
theorem alternatingFactorialCounterexample_stepRatio_tendsto_one :
    Tendsto
      (fun k ↦
        ‖alternatingFactorialCounterexample (k + 1) - alternatingFactorialCounterexample k‖ /
          ‖alternatingFactorialCounterexample k‖)
      atTop (nhds 1) := by
  have hbound :
      ∀ k : ℕ,
        ‖‖alternatingFactorialCounterexample (k + 1) -
              alternatingFactorialCounterexample k‖ /
            ‖alternatingFactorialCounterexample k‖ - 1‖ ≤
          1 / (k + 1 : ℝ) := by
    intro k
    -- Use the explicit reciprocal tail bound from the pairwise formulas.
    simpa [Real.norm_eq_abs] using
      alternatingFactorialCounterexample_stepRatio_sub_one_le_one_div k
  have hzero :
      Tendsto
        (fun k ↦
          ‖alternatingFactorialCounterexample (k + 1) - alternatingFactorialCounterexample k‖ /
            ‖alternatingFactorialCounterexample k‖ - 1)
        atTop (nhds 0) := by
    refine squeeze_zero_norm hbound ?_
    have htail :
        Tendsto (fun n : ℕ ↦ (((n + 1 : ℕ) : ℝ))⁻¹) atTop (nhds 0) := by
      convert (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1) using 1
      ext n
      simp [Function.comp]
    simpa [Nat.cast_add, one_div] using htail
  -- The bound forces the defect from `1` to vanish.
  simpa using
    hzero.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (nhds 1))

/-- The explicit sequence `alternatingFactorialCounterexample` does not converge
`Q`-superlinearly to `0`. -/
theorem alternatingFactorialCounterexample_not_hasQSuperlinearConvergenceTo_zero :
    ¬ HasQSuperlinearConvergenceTo alternatingFactorialCounterexample 0 := by
  intro hq
  have hsubseq : Tendsto (fun n : ℕ ↦ 2 * n + 1) atTop atTop := by
    -- The odd indices form a cofinal subsequence of `ℕ`.
    exact tendsto_atTop_mono (fun n ↦ by
      simpa [two_mul, add_assoc, add_left_comm, add_comm] using Nat.le_add_right n (n + 1)) tendsto_id
  have hratio_subseq :
      Tendsto (fun n ↦ qErrorRatio alternatingFactorialCounterexample 0 1 (2 * n + 1))
        atTop (nhds 0) := by
    exact hq.ratio_tendsto.comp hsubseq
  have hconst_to_zero :
      Tendsto (fun n : ℕ ↦ (2 : ℝ)) atTop (nhds 0) := by
    convert hratio_subseq using 1
    ext n
    symm
    exact alternatingFactorialCounterexample_qErrorRatio_odd n
  have hconst_to_two :
      Tendsto (fun n : ℕ ↦ (2 : ℝ)) atTop (nhds 2) := tendsto_const_nhds
  -- The same constant sequence cannot converge to both `0` and `2`.
  have : (0 : ℝ) = 2 := tendsto_nhds_unique hconst_to_zero hconst_to_two
  norm_num at this

/-- Chapter01 Theorem 1.5.2 (2): in general, the converse of `(1)` is false; there exists a real
sequence whose normalized step lengths tend to `1` but which does not converge
`Q`-superlinearly to `0`. -/
theorem stepRatio_tendsto_one_not_converse_hasQSuperlinearConvergenceTo :
    ∃ x : ℕ → ℝ,
      Tendsto (fun k ↦ ‖x (k + 1) - x k‖ / ‖x k‖) atTop (nhds 1) ∧
        ¬ HasQSuperlinearConvergenceTo x 0 := by
  -- Package the explicit counterexample established above.
  exact ⟨alternatingFactorialCounterexample,
    alternatingFactorialCounterexample_stepRatio_tendsto_one,
    alternatingFactorialCounterexample_not_hasQSuperlinearConvergenceTo_zero⟩
