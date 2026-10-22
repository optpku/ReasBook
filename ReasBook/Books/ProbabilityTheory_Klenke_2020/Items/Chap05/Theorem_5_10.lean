/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Theorem_5_5

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

/-- Helper for Theorem 5.10: the nat-valued time is almost everywhere measurable once its real cast
is square-integrable. -/
lemma aemeasurable_nat_of_memLp_cast (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (hT_memLp : MemLp (fun ω ↦ (T ω : ℝ)) 2 P) :
    AEMeasurable T P := by
  -- Recover `T` from its real-valued cast using `Nat.floor`.
  convert
      ((show Measurable (Nat.floor : ℝ → ℕ) from Nat.measurable_floor).comp_aemeasurable
        hT_memLp.aestronglyMeasurable.aemeasurable) using 1
  ext ω
  simpa using (Nat.floor_natCast (T ω))

/-- Helper for Theorem 5.10: every deterministic textbook partial sum is square-integrable when
`X 1` is square-integrable and the summands are identically distributed. -/
lemma textbookPartialSum_memLp_two (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_memLp : MemLp (X 1) 2 P) :
    ∀ n, MemLp (partialSum (fun k ↦ X (k + 1)) n) 2 P := by
  intro n
  induction n with
  | zero =>
      rw [show partialSum (fun k ↦ X (k + 1)) 0 = (fun _ : Ω ↦ (0 : ℝ)) by
        funext ω
        simp [partialSum]]
      simpa using (memLp_const (0 : ℝ) : MemLp (fun _ : Ω ↦ (0 : ℝ)) 2 P)
  | succ n ih =>
      have hXn_memLp : MemLp (X (n + 1)) 2 P := (hX_ident n).memLp_iff.mpr hX1_memLp
      -- Add the next `L²` increment using the textbook recursion.
      rw [show partialSum (fun k ↦ X (k + 1)) (n + 1) =
          (fun ω ↦ partialSum (fun k ↦ X (k + 1)) n ω + X (n + 1) ω) from by
            funext ω
            exact textbookPartialSum_succ X n ω]
      exact ih.add hXn_memLp

/-- Helper for Theorem 5.10: the textbook summands appearing in a fixed partial sum are pairwise
independent. -/
lemma textbookPartialSum_pairwise_indep (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P) (n : ℕ) :
    Set.Pairwise ↑(Finset.Icc 1 n) (fun i j ↦ X i ⟂ᵢ[P] X j) := by
  intro i hi j hj hij
  have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hi).1
  have hj_pos : 0 < j := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hj).1
  have hi_succ : i = (i - 1) + 1 := by
    simpa [Nat.sub_eq_iff_eq_add hi_pos.le] using (Nat.succ_pred_eq_of_pos hi_pos).symm
  have hj_succ : j = (j - 1) + 1 := by
    simpa [Nat.sub_eq_iff_eq_add hj_pos.le] using (Nat.succ_pred_eq_of_pos hj_pos).symm
  have hij' : i - 1 ≠ j - 1 := by
    intro h
    apply hij
    rw [hi_succ, hj_succ, h]
  -- Shift the indices back to the `0,1,2,…` convention used by `iIndepFun`.
  have h_ind : X ((i - 1) + 1) ⟂ᵢ[P] X ((j - 1) + 1) := hX_indep.indepFun hij'
  have hi_sub_add : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_of_lt hi_pos)
  have hj_sub_add : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.succ_le_of_lt hj_pos)
  simpa [hi_sub_add, hj_sub_add] using h_ind

/-- Helper for Theorem 5.10: the variance of the deterministic textbook partial sum is
`n * Var[X 1]`. -/
lemma variance_textbookPartialSum_eq_nat_mul_variance (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_memLp : MemLp (X 1) 2 P) :
    ∀ n, Var[partialSum (fun k ↦ X (k + 1)) n; P] = (n : ℝ) * Var[X 1; P] := by
  intro n
  -- Rewrite the partial sum as a finite sum and apply variance additivity for pairwise
  -- independent `L²` summands.
  rw [show partialSum (fun k ↦ X (k + 1)) n = (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω) by
    funext ω
    exact partialSum_textbook_apply X n ω]
  have hsum :
      Var[(∑ i ∈ Finset.Icc 1 n, X i); P] = (n : ℝ) * Var[X 1; P] :=
    (IndepFun.variance_sum
      (fun i hi ↦ by
        have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hi).1
        have hi_sub_add : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_of_lt hi_pos)
        have h_mem : MemLp (X ((i - 1) + 1)) 2 P := (hX_ident (i - 1)).memLp_iff.mpr hX1_memLp
        simpa [hi_sub_add] using h_mem)
      (textbookPartialSum_pairwise_indep P X hX_indep n)).trans <|
      by
        calc
          ∑ i ∈ Finset.Icc 1 n, Var[X i; P]
              = ∑ i ∈ Finset.Icc 1 n, Var[X 1; P] := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  have hi_pos : 0 < i := lt_of_lt_of_le Nat.zero_lt_one (Finset.mem_Icc.mp hi).1
                  have hi_sub_add : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.succ_le_of_lt hi_pos)
                  have h_var : Var[X ((i - 1) + 1); P] = Var[X 1; P] :=
                    (hX_ident (i - 1)).variance_eq
                  simpa [hi_sub_add] using h_var
          _ = ((Finset.Icc 1 n).card : ℝ) * Var[X 1; P] := by
                rw [Finset.sum_const, nsmul_eq_mul]
          _ = (n : ℝ) * Var[X 1; P] := by
                simp
  rw [show (∑ i ∈ Finset.Icc 1 n, X i) = (fun ω ↦ ∑ i ∈ Finset.Icc 1 n, X i ω) by
        funext ω
        simp] at hsum
  exact hsum

/-- Helper for Theorem 5.10: the deterministic second moment of the textbook partial sum has the
closed form from the Blackwell--Girshick computation. -/
lemma second_moment_textbookPartialSum_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P) (hX1_memLp : MemLp (X 1) 2 P) :
    ∀ n : ℕ,
      P[fun ω ↦ (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2] =
        (n : ℝ) * Var[X 1; P] + (n : ℝ) ^ 2 * (P[X 1]) ^ 2 := by
  intro n
  have hSn_memLp := textbookPartialSum_memLp_two P X hX_ident hX1_memLp n
  -- Split the second moment into variance plus squared mean, then identify each part.
  calc
    P[fun ω ↦ (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2]
        = Var[partialSum (fun k ↦ X (k + 1)) n; P] +
            P[partialSum (fun k ↦ X (k + 1)) n] ^ 2 := by
            have hvar :=
              congrArg (fun r : ℝ ↦ r + P[partialSum (fun k ↦ X (k + 1)) n] ^ 2)
                (variance_eq_sub hSn_memLp)
            ring_nf at hvar
            simpa [Pi.pow_apply, Nat.add_comm] using hvar.symm
    _ = (n : ℝ) * Var[X 1; P] + ((n : ℝ) * P[X 1]) ^ 2 := by
          rw [variance_textbookPartialSum_eq_nat_mul_variance P X hX_indep hX_ident hX1_memLp n,
            integral_textbookPartialSum_eq_nat_mul_expectation P X hX_ident
              (hX1_memLp.integrable one_le_two) n]
    _ = (n : ℝ) * Var[X 1; P] + (n : ℝ) ^ 2 * (P[X 1]) ^ 2 := by
          ring

/-- Helper for Theorem 5.10: squaring preserves the independence of a deterministic textbook
partial sum from the time atom `{T = n}`. -/
lemma textbookPartialSum_sq_indep_time_atom (P : Measure Ω) [IsProbabilityMeasure P] (T : Ω → ℕ)
    (X : ℕ → Ω → ℝ) (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω)) (n : ℕ) :
    (fun ω ↦ (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2) ⟂ᵢ[P]
      (fun ω ↦ if T ω = n then (1 : ℝ) else 0) := by
  -- Compose the time-atom independence with the measurable squaring map.
  simpa [Function.comp] using
    (textbookPartialSum_indep_time_atom P T X hTX_indep n).comp
      (measurable_id.pow_const (2 : ℕ)) measurable_id

/-- Helper for Theorem 5.10: each finite square truncation factors into the first two moments of
the counting variable. -/
lemma integral_stopped_square_truncation_eq_time_moments (P : Measure Ω)
    [IsProbabilityMeasure P] (T : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_memLp : MemLp (fun ω ↦ (T ω : ℝ)) 2 P) (hX1_memLp : MemLp (X 1) 2 P) (N : ℕ) :
    ∫ ω, ∑ n ∈ Finset.range (N + 1),
        (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P =
      Var[X 1; P] *
          ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P +
        (P[X 1]) ^ 2 *
          ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P := by
  have hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P := hT_memLp.integrable one_le_two
  have hterm_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable (fun ω ↦
          (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2 * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    -- Each square term is integrable, and the time atom is bounded.
    exact ProbabilityTheory.IndepFun.integrable_mul
      (textbookPartialSum_sq_indep_time_atom P T X hTX_indep n)
      ((textbookPartialSum_memLp_two P X hX_ident hX1_memLp n).integrable_sq)
      (time_atom_integrable P T hT_int n)
  have hW1_term_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable (fun ω ↦ (n : ℝ) * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    exact (time_atom_integrable P T hT_int n).const_mul (n : ℝ)
  have hW2_term_int :
      ∀ n ∈ Finset.range (N + 1),
        Integrable (fun ω ↦ (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0)) P := by
    intro n hn
    exact (time_atom_integrable P T hT_int n).const_mul ((n : ℝ) ^ 2)
  -- Expand the finite square truncation, factor each atom by independence, and insert the closed
  -- formula for the deterministic second moment.
  rw [integral_finset_sum _ hterm_int]
  calc
    ∑ n ∈ Finset.range (N + 1),
        ∫ ω, (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P
        = ∑ n ∈ Finset.range (N + 1),
            ((∫ ω, (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2 ∂P) *
              ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            have hsq_int : Integrable (fun ω ↦ (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2) P :=
              (textbookPartialSum_memLp_two P X hX_ident hX1_memLp n).integrable_sq
            simpa using ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral
              (textbookPartialSum_sq_indep_time_atom P T X hTX_indep n)
              hsq_int.aestronglyMeasurable
              (time_atom_aestronglyMeasurable P T hT_int n)
    _ = ∑ n ∈ Finset.range (N + 1),
          (((n : ℝ) * Var[X 1; P] + (n : ℝ) ^ 2 * (P[X 1]) ^ 2) *
            ∫ ω, (if T ω = n then (1 : ℝ) else 0) ∂P) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [second_moment_textbookPartialSum_eq P X hX_indep hX_ident hX1_memLp n]
    _ = ∑ n ∈ Finset.range (N + 1),
          (Var[X 1; P] * ∫ ω, (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P +
            (P[X 1]) ^ 2 * ∫ ω, (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
          ring
    _ = Var[X 1; P] *
          ∑ n ∈ Finset.range (N + 1),
            ∫ ω, (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P +
        (P[X 1]) ^ 2 *
          ∑ n ∈ Finset.range (N + 1),
            ∫ ω, (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ = Var[X 1; P] *
          ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0) ∂P +
        (P[X 1]) ^ 2 *
          ∫ ω, ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0) ∂P := by
          rw [integral_finset_sum _ hW1_term_int, integral_finset_sum _ hW2_term_int]

/-- Helper for Theorem 5.10: the stopped square is integrable and its expectation has the
Blackwell--Girshick second-moment form. -/
lemma stopped_square_integrable_and_integral_eq (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_memLp : MemLp (fun ω ↦ (T ω : ℝ)) 2 P) (hX1_memLp : MemLp (X 1) 2 P) :
    Integrable
        (fun ω ↦
          (stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ)) ω) ^ 2) P ∧
      P[fun ω ↦
          (stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ)) ω) ^ 2] =
        P[fun ω ↦ (T ω : ℝ)] * Var[X 1; P] +
          P[fun ω ↦ ((T ω : ℝ) ^ 2)] * (P[X 1]) ^ 2 := by
  let Y : Ω → ℝ := stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ))
  let F2 : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1),
      (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2 * (if T ω = n then (1 : ℝ) else 0)
  let W1 : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) * (if T ω = n then (1 : ℝ) else 0)
  let W2 : ℕ → Ω → ℝ := fun N ω ↦
    ∑ n ∈ Finset.range (N + 1), (n : ℝ) ^ 2 * (if T ω = n then (1 : ℝ) else 0)
  have hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P := hT_memLp.integrable one_le_two
  have hT_sq_int : Integrable (fun ω ↦ ((T ω : ℝ) ^ 2)) P := hT_memLp.integrable_sq
  have hX1_int : Integrable (X 1) P := hX1_memLp.integrable one_le_two
  have hY_eq : Y = fun ω ↦ partialSum (fun k ↦ X (k + 1)) (T ω) ω := by
    funext ω
    change partialSum (fun k ↦ X (k + 1)) ((T ω : WithTop ℕ)).untopA ω =
      partialSum (fun k ↦ X (k + 1)) (T ω) ω
    rfl
  have hY_int : Integrable Y P := by
    -- Reuse Wald's identity to get the basic measurability and `L¹` control of the stopped sum.
    simpa [Y] using (wald_identity P T X hTX_indep hX_ident hT_int hX1_int).1
  have hF2_int : ∀ N, Integrable (F2 N) P := by
    intro N
    -- Each square truncation is a finite sum of integrable atom contributions.
    exact integrable_finset_sum _ fun n hn ↦
      ProbabilityTheory.IndepFun.integrable_mul
        (textbookPartialSum_sq_indep_time_atom P T X hTX_indep n)
        ((textbookPartialSum_memLp_two P X hX_ident hX1_memLp n).integrable_sq)
        (time_atom_integrable P T hT_int n)
  have hF2_eq : ∀ N ω, F2 N ω = if T ω ≤ N then (Y ω) ^ 2 else 0 := by
    intro N ω
    -- Collapse the atom sum to the unique active time fiber and identify the stopped square.
    simpa [F2, hY_eq] using
      (sum_range_mul_time_atom_eq_if_le
        (fun n ↦ (partialSum (fun k ↦ X (k + 1)) n ω) ^ 2) N (T ω))
  have hW1_eq : ∀ N ω, W1 N ω = if T ω ≤ N then (T ω : ℝ) else 0 := by
    intro N ω
    -- The first-moment truncation is the cutoff version of the time variable itself.
    simpa [W1] using (sum_range_mul_time_atom_eq_if_le (fun n ↦ (n : ℝ)) N (T ω))
  have hW2_eq : ∀ N ω, W2 N ω = if T ω ≤ N then ((T ω : ℝ) ^ 2) else 0 := by
    intro N ω
    -- The second-moment truncation is the cutoff version of the squared time variable.
    simpa [W2] using (sum_range_mul_time_atom_eq_if_le (fun n ↦ (n : ℝ) ^ 2) N (T ω))
  have hW1_int : ∀ N, Integrable (W1 N) P := by
    intro N
    have hχ_meas : Measurable (fun x : ℝ ↦ if x ≤ N then x else 0) := by
      refine Measurable.ite ?_ measurable_id measurable_const
      exact (isClosed_le continuous_id continuous_const).measurableSet
    have hW1_aesm : AEStronglyMeasurable (W1 N) P := by
      have hcomp :
          AEStronglyMeasurable ((fun x : ℝ ↦ if x ≤ N then x else 0) ∘ fun ω ↦ (T ω : ℝ)) P :=
        (hχ_meas.comp_aemeasurable hT_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      have hcomp_eq :
          ((fun x : ℝ ↦ if x ≤ N then x else 0) ∘ fun ω ↦ (T ω : ℝ)) = W1 N := by
        funext ω
        simp [hW1_eq N ω]
      simpa [hcomp_eq] using hcomp
    -- The cutoff time variable is dominated by the original integrable time variable.
    refine Integrable.mono' hT_int hW1_aesm ?_
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW1_eq N ω, h]
    · simp [hW1_eq N ω, h]
  have hW2_int : ∀ N, Integrable (W2 N) P := by
    intro N
    have hχ_meas : Measurable (fun x : ℝ ↦ if x ≤ N then x ^ 2 else 0) := by
      refine Measurable.ite ?_ (measurable_id.pow_const (2 : ℕ)) measurable_const
      exact (isClosed_le continuous_id continuous_const).measurableSet
    have hW2_aesm : AEStronglyMeasurable (W2 N) P := by
      have hcomp :
          AEStronglyMeasurable
            ((fun x : ℝ ↦ if x ≤ N then x ^ 2 else 0) ∘ fun ω ↦ (T ω : ℝ)) P :=
        (hχ_meas.comp_aemeasurable hT_int.aestronglyMeasurable.aemeasurable).aestronglyMeasurable
      have hcomp_eq :
          ((fun x : ℝ ↦ if x ≤ N then x ^ 2 else 0) ∘ fun ω ↦ (T ω : ℝ)) = W2 N := by
        funext ω
        simp [hW2_eq N ω]
      simpa [hcomp_eq] using hcomp
    -- The squared cutoff is dominated by the square of the integrable time variable.
    refine Integrable.mono' hT_sq_int hW2_aesm ?_
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW2_eq N ω, h]
    · simp [hW2_eq N ω, h]
  have hF2_nonneg : ∀ N, ∀ᵐ ω ∂P, 0 ≤ F2 N ω := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hF2_eq N ω, h, sq_nonneg]
    · simp [hF2_eq N ω, h]
  have hF2_lintegral_tendsto :
      Filter.Tendsto
        (fun N ↦ ∫⁻ ω, ENNReal.ofReal (F2 N ω) ∂P) Filter.atTop
        (nhds (∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P)) := by
    -- Route correction: the global atom truncations make the square limit eventually constant on
    -- each sample path, so monotone convergence applies directly.
    refine MeasureTheory.lintegral_tendsto_of_tendsto_of_monotone ?_ ?_ ?_
    · intro N
      exact ENNReal.measurable_ofReal.comp_aemeasurable
        (hF2_int N).aestronglyMeasurable.aemeasurable
    · filter_upwards with ω
      intro m n hmn
      by_cases hm : T ω ≤ m
      · have hn : T ω ≤ n := le_trans hm hmn
        simp [hF2_eq, hm, hn]
      · by_cases hn : T ω ≤ n
        · simp [hF2_eq, hm, hn]
        · simp [hF2_eq, hm, hn]
    · filter_upwards with ω
      have hEq :
          (fun _ : ℕ ↦ ENNReal.ofReal ((Y ω) ^ 2)) =ᶠ[Filter.atTop]
            fun N ↦ ENNReal.ofReal (F2 N ω) := by
        refine Filter.eventually_atTop.2 ?_
        refine ⟨T ω, ?_⟩
        intro N hN
        simp [hF2_eq, hN]
      exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hW1_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun N ↦ W1 N ω) Filter.atTop (nhds (T ω : ℝ)) := by
    filter_upwards with ω
    have hEq : (fun _ : ℕ ↦ (T ω : ℝ)) =ᶠ[Filter.atTop] fun N ↦ W1 N ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨T ω, ?_⟩
      intro N hN
      simp [hW1_eq, hN]
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hW2_tendsto :
      ∀ᵐ ω ∂P, Filter.Tendsto (fun N ↦ W2 N ω) Filter.atTop (nhds ((T ω : ℝ) ^ 2)) := by
    filter_upwards with ω
    have hEq : (fun _ : ℕ ↦ ((T ω : ℝ) ^ 2)) =ᶠ[Filter.atTop] fun N ↦ W2 N ω := by
      refine Filter.eventually_atTop.2 ?_
      refine ⟨T ω, ?_⟩
      intro N hN
      simp [hW2_eq, hN]
    exact Filter.Tendsto.congr' hEq tendsto_const_nhds
  have hW1_bound : ∀ N, ∀ᵐ ω ∂P, ‖W1 N ω‖ ≤ (T ω : ℝ) := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW1_eq N ω, h]
    · simp [hW1_eq N ω, h]
  have hW2_bound : ∀ N, ∀ᵐ ω ∂P, ‖W2 N ω‖ ≤ ((T ω : ℝ) ^ 2) := by
    intro N
    filter_upwards with ω
    by_cases h : T ω ≤ N
    · simp [hW2_eq N ω, h]
    · simp [hW2_eq N ω, h]
  have hW1_integral_tendsto :
      Filter.Tendsto (fun N ↦ ∫ ω, W1 N ω ∂P) Filter.atTop
        (nhds (∫ ω, (T ω : ℝ) ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω ↦ (T ω : ℝ))
      (fun N ↦ (hW1_int N).aestronglyMeasurable) hT_int hW1_bound hW1_tendsto
  have hW2_integral_tendsto :
      Filter.Tendsto (fun N ↦ ∫ ω, W2 N ω ∂P) Filter.atTop
        (nhds (∫ ω, ((T ω : ℝ) ^ 2) ∂P)) := by
    exact MeasureTheory.tendsto_integral_of_dominated_convergence (fun ω ↦ (T ω : ℝ) ^ 2)
      (fun N ↦ (hW2_int N).aestronglyMeasurable) hT_sq_int hW2_bound hW2_tendsto
  let L : ℝ :=
    (∫ ω, (T ω : ℝ) ∂P) * Var[X 1; P] + (∫ ω, ((T ω : ℝ) ^ 2) ∂P) * (∫ ω, X 1 ω ∂P) ^ 2
  have htrunc_eq :
      (fun N ↦ ∫ ω, F2 N ω ∂P) =ᶠ[Filter.atTop]
        fun N ↦
          Var[X 1; P] * ∫ ω, W1 N ω ∂P +
            (∫ ω, X 1 ω ∂P) ^ 2 * ∫ ω, W2 N ω ∂P := by
    exact Filter.Eventually.of_forall fun N ↦ by
      simpa [F2, W1, W2] using
        integral_stopped_square_truncation_eq_time_moments
          P T X hTX_indep hX_indep hX_ident hT_memLp hX1_memLp N
  have hright_tendsto :
      Filter.Tendsto
        (fun N ↦
          Var[X 1; P] * ∫ ω, W1 N ω ∂P +
            (∫ ω, X 1 ω ∂P) ^ 2 * ∫ ω, W2 N ω ∂P) Filter.atTop (nhds L) := by
    simpa [L, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
      (Filter.Tendsto.const_mul (Var[X 1; P]) hW1_integral_tendsto).add
        (Filter.Tendsto.const_mul ((∫ ω, X 1 ω ∂P) ^ 2) hW2_integral_tendsto)
  have hF2_integral_tendsto :
      Filter.Tendsto (fun N ↦ ∫ ω, F2 N ω ∂P) Filter.atTop (nhds L) := by
    exact Filter.Tendsto.congr' htrunc_eq.symm hright_tendsto
  have htrunc_lintegral_eq :
      (fun N ↦ ∫⁻ ω, ENNReal.ofReal (F2 N ω) ∂P) =ᶠ[Filter.atTop]
        fun N ↦
          ENNReal.ofReal
            (Var[X 1; P] * ∫ ω, W1 N ω ∂P +
              (∫ ω, X 1 ω ∂P) ^ 2 * ∫ ω, W2 N ω ∂P) := by
    exact Filter.Eventually.of_forall fun N ↦ by
      calc
        ∫⁻ ω, ENNReal.ofReal (F2 N ω) ∂P = ENNReal.ofReal (∫ ω, F2 N ω ∂P) := by
          symm
          exact MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF2_int N) (hF2_nonneg N)
        _ = ENNReal.ofReal
              (Var[X 1; P] * ∫ ω, W1 N ω ∂P + (∫ ω, X 1 ω ∂P) ^ 2 * ∫ ω, W2 N ω ∂P) := by
            congr 1
            simpa [F2, W1, W2] using
              integral_stopped_square_truncation_eq_time_moments
                P T X hTX_indep hX_indep hX_ident hT_memLp hX1_memLp N
  have hright_ennreal_tendsto :
      Filter.Tendsto
        (fun N ↦
          ENNReal.ofReal
            (Var[X 1; P] * ∫ ω, W1 N ω ∂P +
              (∫ ω, X 1 ω ∂P) ^ 2 * ∫ ω, W2 N ω ∂P)) Filter.atTop
        (nhds (ENNReal.ofReal L)) := by
    exact ENNReal.tendsto_ofReal hright_tendsto
  have h_lintegral_eq :
      ∫⁻ ω, ENNReal.ofReal ((Y ω) ^ 2) ∂P = ENNReal.ofReal L := by
    exact tendsto_nhds_unique
      (Filter.Tendsto.congr' htrunc_lintegral_eq hF2_lintegral_tendsto) hright_ennreal_tendsto
  have hYsq_nonneg : ∀ᵐ ω ∂P, 0 ≤ (Y ω) ^ 2 := by
    exact Filter.Eventually.of_forall fun ω ↦ sq_nonneg (Y ω)
  have hYsq_aesm : AEStronglyMeasurable (fun ω ↦ (Y ω) ^ 2) P := by
    have hY_meas : AEMeasurable Y P := hY_int.aestronglyMeasurable.aemeasurable
    exact (hY_meas.pow_const (2 : ℕ)).aestronglyMeasurable
  have hYsq_hfi : HasFiniteIntegral (fun ω ↦ (Y ω) ^ 2) P := by
    rw [MeasureTheory.hasFiniteIntegral_iff_ofReal hYsq_nonneg, h_lintegral_eq]
    exact ENNReal.ofReal_lt_top
  have hYsq_int : Integrable (fun ω ↦ (Y ω) ^ 2) P := ⟨hYsq_aesm, hYsq_hfi⟩
  have hT_nonneg : 0 ≤ ∫ ω, (T ω : ℝ) ∂P := by
    exact integral_nonneg fun ω ↦ Nat.cast_nonneg (T ω)
  have hTsq_nonneg : 0 ≤ ∫ ω, ((T ω : ℝ) ^ 2) ∂P := by
    exact integral_nonneg fun ω ↦ sq_nonneg ((T ω : ℝ))
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    refine add_nonneg ?_ ?_
    · exact mul_nonneg hT_nonneg (variance_nonneg (X 1) P)
    · exact mul_nonneg hTsq_nonneg (sq_nonneg (∫ ω, X 1 ω ∂P))
  have h_second_moment :
      ∫ ω, (Y ω) ^ 2 ∂P = L := by
    have h_ofReal :
        ENNReal.ofReal (∫ ω, (Y ω) ^ 2 ∂P) = ENNReal.ofReal L := by
      rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hYsq_int hYsq_nonneg, h_lintegral_eq]
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω ↦ sq_nonneg (Y ω)) hL_nonneg).1
      h_ofReal
  exact ⟨by simpa [Y] using hYsq_int, by simpa [Y, L, mul_comm, mul_left_comm, mul_assoc] using h_second_moment⟩

-- Proof sketch: combine Wald's identity for the stopped value of `textbookPartialSum X` at `T`
-- with the second-moment computation obtained by conditioning on the events `{T = n}`; rewrite
-- `E[S_T^2] - E[S_T]^2` in terms of `Var[T]` and `Var[X 1]`.
/-- Theorem 5.10: under the Blackwell--Girshick hypotheses, the stopped sum
`S_T = ∑_{i=1}^{T} X_i` is square integrable, and its variance is
`𝔼[X₁]^2 Var[T] + 𝔼[T] Var[X₁]`. -/
theorem blackwell_girshick_variance_formula (P : Measure Ω) [IsProbabilityMeasure P]
    (T : Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hTX_indep : T ⟂ᵢ[P] (fun ω ↦ fun n ↦ X (n + 1) ω))
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hT_memLp : MemLp (fun ω ↦ (T ω : ℝ)) 2 P) (hX1_memLp : MemLp (X 1) 2 P) :
    MemLp (stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ))) 2 P ∧
      Var[stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ)); P] =
        (P[X 1]) ^ 2 * Var[fun ω ↦ (T ω : ℝ); P] +
          P[fun ω ↦ (T ω : ℝ)] * Var[X 1; P] := by
  let Y : Ω → ℝ := stoppedValue (partialSum (fun k ↦ X (k + 1))) (fun ω ↦ (T ω : WithTop ℕ))
  have hT_int : Integrable (fun ω ↦ (T ω : ℝ)) P := hT_memLp.integrable one_le_two
  have hX1_int : Integrable (X 1) P := hX1_memLp.integrable one_le_two
  obtain ⟨hY_int, hY_mean⟩ :=
    wald_identity P T X hTX_indep hX_ident hT_int hX1_int
  obtain ⟨hYsq_int, hY_second⟩ :=
    stopped_square_integrable_and_integral_eq
      P T X hTX_indep hX_indep hX_ident hT_memLp hX1_memLp
  have hY_memLp : MemLp Y 2 P := by
    -- Upgrade the stopped sum from `L¹` to `L²` using the computed integrable square.
    exact (MeasureTheory.memLp_two_iff_integrable_sq hY_int.aestronglyMeasurable).2 hYsq_int
  refine ⟨by simpa [Y] using hY_memLp, ?_⟩
  -- Combine the second-moment formula with Wald's identity and rewrite the residual term as
  -- `Var[T]`.
  calc
    Var[Y; P] = P[fun ω ↦ (Y ω) ^ 2] - P[Y] ^ 2 := by
      simpa [Y] using (variance_eq_sub hY_memLp)
    _ = (P[fun ω ↦ (T ω : ℝ)] * Var[X 1; P] +
          P[fun ω ↦ ((T ω : ℝ) ^ 2)] * (P[X 1]) ^ 2) -
        (P[fun ω ↦ (T ω : ℝ)] * P[X 1]) ^ 2 := by
          rw [hY_second, hY_mean]
    _ = (P[X 1]) ^ 2 * (P[fun ω ↦ ((T ω : ℝ) ^ 2)] - P[fun ω ↦ (T ω : ℝ)] ^ 2) +
          P[fun ω ↦ (T ω : ℝ)] * Var[X 1; P] := by
          ring
    _ = (P[X 1]) ^ 2 * Var[fun ω ↦ (T ω : ℝ); P] +
          P[fun ω ↦ (T ω : ℝ)] * Var[X 1; P] := by
          have hVarT :
              Var[fun ω ↦ (T ω : ℝ); P] =
                P[fun ω ↦ ((T ω : ℝ) ^ 2)] - P[fun ω ↦ (T ω : ℝ)] ^ 2 := by
            simpa [Pi.pow_apply] using
              (variance_eq_sub hT_memLp)
          rw [hVarT]
