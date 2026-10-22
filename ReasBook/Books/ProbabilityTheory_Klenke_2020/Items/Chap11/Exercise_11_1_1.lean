/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_1
import Books.ProbabilityTheory_Klenke_2020.Items.Chap11.Theorem_11_2

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Finset

universe u

variable {Ω : Type u} {m0 : MeasurableSpace Ω}
variable [m0]
variable {μ : Measure Ω} [IsFiniteMeasure μ]
variable {ℱ : Filtration ℕ m0}

local macro:max "absMaxUpTo(" X:term ", " n:term ", " ω:term ")" : term =>
  `((range ($n + 1)).sup' nonempty_range_add_one fun k ↦ |($X k $ω)|)

/- Exercise 11.1.1 is a `source-facing` maximal-inequality corollary in the discrete-time
martingale domain. The owner abstraction for the maximal event is the canonical running maximum
already used by `MeasureTheory.maximal_ineq`, while the chapter-level bridge layer is
`doobLp_tail_bound` together with the canonical Doob decomposition and its predictable-part
monotonicity criterion from Theorem 10.1. This exercise therefore stays `source-facing`: it keeps
the textbook absolute-maximal tail inequality but relies on those owner declarations rather than a
parallel local wrapper. -/
recall MeasureTheory.maximal_ineq
recall doobLp_tail_bound
recall canonical_doobDecomposition
recall submartingale_ae_monotone_predictablePart

/-- Helper for Exercise 11.1.1: the canonical predictable part of a submartingale is
almost surely nonnegative at every deterministic time. -/
lemma predictablePart_nonneg_ae_of_submartingale {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (n : ℕ) :
    0 ≤ᵐ[μ] fun ω ↦ predictablePart X ℱ μ n ω := by
  -- Proof comment: monotonicity starts from time `0`, where the predictable part vanishes.
  filter_upwards [submartingale_ae_monotone_predictablePart (X := X) (μ := μ) (ℱ := ℱ) hX] with
    ω hω
  simpa [predictablePart_zero] using hω (Nat.zero_le n)

/-- Helper for Exercise 11.1.1: pathwise up to a null set, the running absolute maximum of a
submartingale is controlled by the running absolute maximum of its martingale part plus the
terminal predictable part. -/
lemma absMaxUpTo_le_absMaxUpTo_martingalePart_add_predictablePart {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (n : ℕ) :
    ∀ᵐ ω ∂μ, absMaxUpTo(X, n, ω) ≤
      absMaxUpTo(martingalePart X ℱ μ, n, ω) + predictablePart X ℱ μ n ω := by
  -- Proof comment: use the Doob decomposition pointwise and bound every predictable slice by its
  -- terminal value via the almost-sure monotonicity of the predictable part.
  filter_upwards [submartingale_ae_monotone_predictablePart (X := X) (μ := μ) (ℱ := ℱ) hX] with
    ω hω
  change (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ |X k ω|) ≤
    (range (n + 1)).sup' nonempty_range_add_one (fun k ↦ |martingalePart X ℱ μ k ω|) +
      predictablePart X ℱ μ n ω
  exact Finset.sup'_le nonempty_range_add_one (fun k ↦ |X k ω|) fun (k : ℕ) hk ↦ by
    have hk_le : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    have hA_nonneg : 0 ≤ predictablePart X ℱ μ k ω := by
      simpa [predictablePart_zero] using hω (Nat.zero_le k)
    have hA_le : predictablePart X ℱ μ k ω ≤ predictablePart X ℱ μ n ω := hω hk_le
    have hdecomp :
        X k ω = martingalePart X ℱ μ k ω + predictablePart X ℱ μ k ω := by
      simpa [Pi.add_apply] using
        (congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) k) ω).symm
    have htriangle :
        |martingalePart X ℱ μ k ω + predictablePart X ℱ μ k ω| ≤
          |martingalePart X ℱ μ k ω| + predictablePart X ℱ μ k ω := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_of_nonneg hA_nonneg] using
        (_root_.abs_sub_le
          (martingalePart X ℱ μ k ω + predictablePart X ℱ μ k ω)
          (martingalePart X ℱ μ k ω) 0)
    have hterminal :
        |martingalePart X ℱ μ k ω| + predictablePart X ℱ μ k ω ≤
          |martingalePart X ℱ μ k ω| + predictablePart X ℱ μ n ω := by
      linarith
    have hsup :
        |martingalePart X ℱ μ k ω| ≤
          (range (n + 1)).sup' nonempty_range_add_one (fun j ↦ |martingalePart X ℱ μ j ω|) := by
      exact Finset.le_sup' (s := range (n + 1)) (f := fun j ↦ |martingalePart X ℱ μ j ω|)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk_le))
    calc
      |X k ω| = |martingalePart X ℱ μ k ω + predictablePart X ℱ μ k ω| := by rw [hdecomp]
      _ ≤ |martingalePart X ℱ μ k ω| + predictablePart X ℱ μ n ω := htriangle.trans hterminal
      _ ≤ (range (n + 1)).sup' nonempty_range_add_one (fun j ↦ |martingalePart X ℱ μ j ω|) +
            predictablePart X ℱ μ n ω := by
        linarith

/-- Helper for Exercise 11.1.1: the expectation of the canonical predictable part at time `n`
is bounded by the initial and terminal absolute expectations of the source submartingale. -/
lemma predictablePart_expectation_le_initialAbs_add_terminalAbs {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (n : ℕ) :
    μ[fun ω ↦ predictablePart X ℱ μ n ω] ≤
      μ[fun ω ↦ |X 0 ω|] + μ[fun ω ↦ |X n ω|] := by
  let M : ℕ → Ω → ℝ := martingalePart X ℱ μ
  have hM : Martingale M ℱ μ := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hM0 : M 0 = X 0 := by
    -- Proof comment: at time `0`, the predictable part vanishes, so the martingale part is `X₀`.
    ext ω
    have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) 0) ω
    simpa [M, Pi.add_apply, predictablePart_zero] using hω
  have hA_eq : (fun ω ↦ predictablePart X ℱ μ n ω) = X n - M n := by
    -- Proof comment: solve the Doob decomposition identity for the predictable part at time `n`.
    funext ω
    have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) n) ω
    exact eq_sub_iff_add_eq.mpr (by simpa [M, Pi.add_apply, add_comm] using hω)
  have hA_int : Integrable (fun ω ↦ predictablePart X ℱ μ n ω) μ := by
    -- Proof comment: the predictable part is the difference between `X_n` and the martingale part.
    rw [hA_eq]
    simpa [Pi.sub_apply] using (hX.integrable n).sub (hM.integrable n)
  have hM_integral_eq : μ[M n] = μ[X 0] := by
    -- Proof comment: deterministic-time expectations of a martingale are constant.
    calc
      μ[M n] = μ[M 0] := by
        symm
        simpa [MeasureTheory.setIntegral_univ] using
          hM.setIntegral_eq (Nat.zero_le n) MeasurableSet.univ
      _ = μ[X 0] := by simpa [hM0]
  have hsum_bound :
      |μ[X n]| + |μ[X 0]| ≤ μ[fun ω ↦ |X 0 ω|] + μ[fun ω ↦ |X n ω|] := by
    have hXn_bound : |μ[X n]| ≤ μ[fun ω ↦ |X n ω|] := abs_integral_le_integral_abs (f := X n)
    have hX0_bound : |μ[X 0]| ≤ μ[fun ω ↦ |X 0 ω|] := abs_integral_le_integral_abs (f := X 0)
    linarith
  have hsplit_integral :
      μ[fun ω ↦ predictablePart X ℱ μ n ω] = μ[X n] - μ[M n] := by
    rw [hA_eq]
    simpa [Pi.sub_apply] using integral_sub (hX.integrable n) (hM.integrable n)
  have htriangle :
      μ[X n] - μ[M n] ≤ |μ[X n]| + |μ[X 0]| := by
    have hleft : μ[X n] ≤ |μ[X n]| := le_abs_self _
    have hright : -μ[M n] ≤ |μ[X 0]| := by
      rw [hM_integral_eq]
      simpa using (neg_le_abs (μ[X 0]))
    linarith
  have hfirst :
      μ[fun ω ↦ predictablePart X ℱ μ n ω] ≤ |μ[X n]| + |μ[X 0]| := by
    rw [hsplit_integral]
    exact htriangle
  exact hfirst.trans hsum_bound

/-- Helper for Exercise 11.1.1: negating the process does not change the running absolute
maximum. -/
lemma absMaxUpTo_neg (X : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) :
    absMaxUpTo((-X), n, ω) = absMaxUpTo(X, n, ω) := by
  -- Proof comment: each term of the finite supremum is unchanged because `|-(X k ω)| = |X k ω|`.
  simp [Pi.neg_apply, abs_neg]

/-- Helper for Exercise 11.1.1: the submartingale branch already satisfies the stronger real-valued
estimate with constants `4` and `6`. -/
lemma submartingale_absMaxUpTo_tail_bound_real {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ) (n : ℕ) (c : NNReal) (hc : 0 < c) :
    (c : ℝ) * μ.real {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)} ≤
      4 * μ[fun ω ↦ |X 0 ω|] + 6 * μ[fun ω ↦ |X n ω|] := by
  let M : ℕ → Ω → ℝ := martingalePart X ℱ μ
  let A : ℕ → Ω → ℝ := predictablePart X ℱ μ
  let E : Set Ω := {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)}
  let EM : Set Ω := {ω | (c : ℝ) / 2 ≤ absMaxUpTo(M, n, ω)}
  let EA : Set Ω := {ω | (c : ℝ) / 2 ≤ A n ω}
  have hc_real : 0 < (c : ℝ) := by exact_mod_cast hc
  have hhalf_pos : 0 < (c : ℝ) / 2 := by positivity
  have hM : Martingale M ℱ μ := martingale_martingalePart hX.stronglyAdapted hX.integrable
  have hM_abs : Submartingale (fun i ω ↦ |M i ω|) ℱ μ := martingaleAbsSubmartingale hM
  have hA_nonneg : 0 ≤ᵐ[μ] fun ω ↦ A n ω := by
    simpa [A] using predictablePart_nonneg_ae_of_submartingale (X := X) (μ := μ) (ℱ := ℱ) hX n
  have hA_eq : (fun ω ↦ A n ω) = X n - M n := by
    -- Proof comment: rewrite the terminal predictable part through the Doob decomposition.
    funext ω
    have hω := congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) n) ω
    exact eq_sub_iff_add_eq.mpr (by simpa [M, A, Pi.add_apply, add_comm] using hω)
  have hA_int : Integrable (fun ω ↦ A n ω) μ := by
    -- Proof comment: integrability of the predictable part follows from the integrability of `X_n`
    -- and the martingale part.
    rw [hA_eq]
    simpa [Pi.sub_apply] using (hX.integrable n).sub (hM.integrable n)
  have hM_abs_int : Integrable (fun ω ↦ |M n ω|) μ := by
    simpa [Real.norm_eq_abs] using (hM.integrable n).norm
  have hX_abs_int : Integrable (fun ω ↦ |X n ω|) μ := by
    simpa [Real.norm_eq_abs] using (hX.integrable n).norm
  have hmartingale_event :
      ((c : ℝ) / 2) * μ.real EM ≤ μ[fun ω ↦ |M n ω|] := by
    -- Proof comment: apply the maximal event bound to the nonnegative submartingale `|M|`.
    have hbase :
        ((c : ℝ) / 2) * μ.real EM ≤ ∫ ω in EM, |M n ω| ∂μ := by
      simpa [EM, M, abs_abs] using
        (submartingale_maximal_event_expectation_bounds
          (X := fun i ω ↦ |M i ω|) hM_abs n hhalf_pos).1
    exact hbase.trans <|
      integral_mono_measure μ.restrict_le_self (ae_of_all _ fun ω ↦ abs_nonneg (M n ω))
        hM_abs_int
  have hpredictable_event :
      ((c : ℝ) / 2) * μ.real EA ≤ μ[fun ω ↦ A n ω] := by
    -- Proof comment: Markov's inequality controls the predictable terminal contribution.
    simpa [EA, A] using
      (MeasureTheory.mul_meas_ge_le_integral_of_nonneg (μ := μ) hA_nonneg hA_int ((c : ℝ) / 2))
  have hsplit_ae : E ≤ᵐ[μ] Set.union EM EA := by
    -- Proof comment: if neither half-threshold event occurs, the pathwise decomposition bound
    -- contradicts membership in the full-threshold event.
    filter_upwards
      [absMaxUpTo_le_absMaxUpTo_martingalePart_add_predictablePart
        (X := X) (μ := μ) (ℱ := ℱ) hX n] with ω hω
    intro hE
    by_cases hEM : (c : ℝ) / 2 ≤ absMaxUpTo(M, n, ω)
    · show ω ∈ Set.union EM EA
      exact Or.inl hEM
    · have hEM' : absMaxUpTo(M, n, ω) < (c : ℝ) / 2 := lt_of_not_ge hEM
      show ω ∈ Set.union EM EA
      right
      have hE' : (c : ℝ) ≤ absMaxUpTo(X, n, ω) := hE
      have hEA : (c : ℝ) / 2 ≤ A n ω := by
        linarith
      exact hEA
  have hmeasure_split : μ.real E ≤ μ.real EM + μ.real EA := by
    calc
      μ.real E ≤ μ.real (Set.union EM EA) := by
        exact ENNReal.toReal_mono (measure_ne_top μ (Set.union EM EA)) (measure_mono_ae hsplit_ae)
      _ ≤ μ.real EM + μ.real EA := MeasureTheory.measureReal_union_le EM EA
  have hscaled_split :
      (c : ℝ) * μ.real E ≤ (c : ℝ) * μ.real EM + (c : ℝ) * μ.real EA := by
    nlinarith
  have hmartingale_scaled : (c : ℝ) * μ.real EM ≤ 2 * μ[fun ω ↦ |M n ω|] := by
    linarith
  have hpredictable_scaled : (c : ℝ) * μ.real EA ≤ 2 * μ[fun ω ↦ A n ω] := by
    linarith
  have hM_pointwise : ∀ᵐ ω ∂μ, |M n ω| ≤ |X n ω| + A n ω := by
    -- Proof comment: rearrange the Doob decomposition and use the nonnegativity of `A_n`.
    filter_upwards [hA_nonneg] with ω hAω
    have hω : M n ω + A n ω = X n ω := by
      simpa [M, A, Pi.add_apply] using congrFun (congrFun (martingalePart_add_predictablePart ℱ μ X) n) ω
    have hsplit : M n ω = X n ω - A n ω := by linarith
    calc
      |M n ω| = |X n ω - A n ω| := by rw [hsplit]
      _ ≤ |X n ω| + |A n ω| := by
        simpa using (_root_.abs_sub_le (X n ω) 0 (A n ω))
      _ = |X n ω| + A n ω := by rw [abs_of_nonneg hAω]
  have hM_expectation :
      μ[fun ω ↦ |M n ω|] ≤ μ[fun ω ↦ |X n ω|] + μ[fun ω ↦ A n ω] := by
    -- Proof comment: integrate the pointwise comparison between `|M_n|` and `|X_n| + A_n`.
    calc
      μ[fun ω ↦ |M n ω|] ≤ μ[fun ω ↦ |X n ω| + A n ω] := by
        exact integral_mono_ae hM_abs_int (hX_abs_int.add hA_int) hM_pointwise
      _ = μ[fun ω ↦ |X n ω|] + μ[fun ω ↦ A n ω] := by
        simpa using integral_add hX_abs_int hA_int
  have hA_expectation :
      μ[fun ω ↦ A n ω] ≤ μ[fun ω ↦ |X 0 ω|] + μ[fun ω ↦ |X n ω|] := by
    simpa [A] using
      predictablePart_expectation_le_initialAbs_add_terminalAbs
        (X := X) (μ := μ) (ℱ := ℱ) hX n
  calc
    (c : ℝ) * μ.real E ≤ 2 * μ[fun ω ↦ |M n ω|] + 2 * μ[fun ω ↦ A n ω] := by
      linarith
    _ ≤ 2 * (μ[fun ω ↦ |X n ω|] + μ[fun ω ↦ A n ω]) + 2 * μ[fun ω ↦ A n ω] := by
      gcongr
    _ = 2 * μ[fun ω ↦ |X n ω|] + 4 * μ[fun ω ↦ A n ω] := by ring
    _ ≤ 2 * μ[fun ω ↦ |X n ω|] +
          4 * (μ[fun ω ↦ |X 0 ω|] + μ[fun ω ↦ |X n ω|]) := by
      gcongr
    _ = 4 * μ[fun ω ↦ |X 0 ω|] + 6 * μ[fun ω ↦ |X n ω|] := by ring

-- Proof sketch: if `X` is a submartingale, combine Doob's decomposition with Theorem 11.2 applied
-- to the martingale part and the predictable monotonicity estimates for the finite-variation part.
-- If `X` is a supermartingale, apply the same argument to `-X`, noting that the running maxima of
-- `|-X|` and `|X|` agree pointwise and that `|(-X) n| = |X n|`.
/-- Exercise 11.1.1: for a real-valued submartingale or supermartingale and a positive threshold,
the tail of the maximal absolute process up to time `n` is bounded by `|X_0|` and `|X_n|` with
constants `12` and `9`. -/
theorem submartingale_or_supermartingale_absMaxUpTo_tail_bound {X : ℕ → Ω → ℝ}
    (hX : Submartingale X ℱ μ ∨ Supermartingale X ℱ μ) (n : ℕ) (c : NNReal) (hc : 0 < c) :
    c * μ {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)} ≤
      ENNReal.ofReal (12 * μ[fun ω ↦ |X 0 ω|] + 9 * μ[fun ω ↦ |X n ω|]) := by
  let E : Set Ω := {ω | (c : ℝ) ≤ absMaxUpTo(X, n, ω)}
  have hX0_nonneg : 0 ≤ μ[fun ω ↦ |X 0 ω|] := by
    -- Proof comment: integrals of nonnegative functions are nonnegative.
    exact integral_nonneg fun ω ↦ abs_nonneg (X 0 ω)
  have hXn_nonneg : 0 ≤ μ[fun ω ↦ |X n ω|] := by
    -- Proof comment: the same positivity applies to the terminal absolute value.
    exact integral_nonneg fun ω ↦ abs_nonneg (X n ω)
  rcases hX with hsub | hsuper
  · -- Proof comment: use the stronger real-valued submartingale estimate and relax the constants.
    have hreal :
        (c : ℝ) * μ.real E ≤ 12 * μ[fun ω ↦ |X 0 ω|] + 9 * μ[fun ω ↦ |X n ω|] := by
      refine (submartingale_absMaxUpTo_tail_bound_real
        (X := X) (μ := μ) (ℱ := ℱ) hsub n c hc).trans ?_
      linarith
    simpa [E, ENNReal.ofReal_mul hc.le, ofReal_measureReal] using
      (ENNReal.ofReal_le_ofReal hreal)
  · -- Route correction: rather than developing a separate supermartingale Doob decomposition, pass
    -- to `-X`, apply the submartingale estimate there, and simplify the absolute quantities.
    have hE_neg : {ω | (c : ℝ) ≤ absMaxUpTo((-X), n, ω)} = E := by
      ext ω
      simp [E, absMaxUpTo_neg]
    have hneg :
        (c : ℝ) * μ.real E ≤ 4 * μ[fun ω ↦ |X 0 ω|] + 6 * μ[fun ω ↦ |X n ω|] := by
      simpa [E, hE_neg, Pi.neg_apply, abs_neg] using
        (submartingale_absMaxUpTo_tail_bound_real
          (X := -X) (μ := μ) (ℱ := ℱ) hsuper.neg n c hc)
    have hreal :
        (c : ℝ) * μ.real E ≤ 12 * μ[fun ω ↦ |X 0 ω|] + 9 * μ[fun ω ↦ |X n ω|] := by
      exact hneg.trans <| by linarith
    simpa [E, ENNReal.ofReal_mul hc.le, ofReal_measureReal] using
      (ENNReal.ofReal_le_ofReal hreal)
