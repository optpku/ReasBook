/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Definition_15_40

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

open RealRandomVariableArray

section IIDStandardizedArray

variable (Y : ℕ → Ω → ℝ) (hY_meas : ∀ n, Measurable (Y n))

/- Example 15.42 is `source-facing`: it constructs the standardized triangular array attached to
an i.i.d. sequence. Its `core/canonical` owner in this chapter is `RealRandomVariableArray Ω`; the
pointwise formula below is only the bridge/view back to the textbook coordinates. -/
/-- Source-facing construction for Example 15.42: from a `0`-based Lean i.i.d. sequence `Y 0,
Y 1, ...` representing the
textbook sequence `Y₁, Y₂, ...`, the `n`-th Lean row models the textbook row `n + 1` and has
entries `Y_i / √(n + 1)`. -/
def iid_standardized_array : RealRandomVariableArray Ω where
  rowLength n := n + 1
  entry n i ω := Y i.1 ω / Real.sqrt (n + 1 : ℝ)
  measurable_entry n i := by
    simpa using (hY_meas i.1).div_const (Real.sqrt (n + 1 : ℝ))

-- Proof sketch: unfold `iid_standardized_array` and read off the defining formula.
/-- The standardized array entry is the `i`-th coordinate divided by `√(n + 1)`. -/
theorem iid_standardized_array_apply (n : ℕ) (i : Fin (n + 1)) (ω : Ω) :
    iid_standardized_array Y hY_meas n i ω = Y i.1 ω / Real.sqrt (n + 1 : ℝ) := rfl

-- Proof sketch: use the measurable-entry field of the owner array.
/-- The entries of the standardized i.i.d. triangular array are measurable. -/
theorem measurable_iid_standardized_array_entry (n : ℕ) (i : Fin (n + 1)) :
    Measurable (iid_standardized_array Y hY_meas n i) :=
  (iid_standardized_array Y hY_meas).measurable_entry n i

variable {Y hY_meas}
variable {P : Measure Ω}

-- Proof sketch: each row is the finite restriction of the independent family `Y`, scaled by the
-- row-constant `√(n + 1)`.
/-- Every row of the standardized array is an independent finite family. -/
theorem iid_standardized_array_isIndependent
    (hY_indep : iIndepFun Y P) :
    IsIndependent (iid_standardized_array Y hY_meas) P := by
  refine ⟨fun n ↦ ?_⟩
  -- Restrict the independent sequence to the current finite row, then scale each coordinate.
  let hrow : iIndepFun (fun i : Fin (n + 1) ↦ Y i.1) P :=
    hY_indep.precomp Fin.val_injective
  let g : Fin (n + 1) → ℝ → ℝ := fun _ x ↦ x / Real.sqrt (n + 1 : ℝ)
  have hg : ∀ i, Measurable (g i) := by
    intro i
    simpa [g] using measurable_id.div_const (Real.sqrt (n + 1 : ℝ))
  simpa [iid_standardized_array_apply, g] using hrow.comp g hg

variable [IsProbabilityMeasure P]

-- Proof sketch: identical distribution transfers centeredness from `Y 0` to every coordinate, and
-- scaling by the deterministic constant `√(n + 1)` preserves mean zero.
/-- The standardized i.i.d. triangular array is centered when the common law is centered. -/
theorem iid_standardized_array_isCentered
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) :
    IsCentered (iid_standardized_array Y hY_meas) P := by
  refine ⟨fun n i ↦ ?_⟩
  rcases hY_centered with ⟨hY0_int, hY0_mean⟩
  have hYi_int : Integrable (Y i.1) P := (hY_ident i.1).integrable_iff.2 hY0_int
  have hYi_mean : P[Y i.1] = 0 := by
    rw [(hY_ident i.1).integral_eq, hY0_mean]
  -- Divide the centered coordinate by the deterministic row scale.
  refine ⟨?_, ?_⟩
  · simpa [iid_standardized_array_apply] using hYi_int.div_const (Real.sqrt (n + 1 : ℝ))
  · -- Rewrite the entry integral through the deterministic row scaling.
    calc
      ∫ ω, iid_standardized_array Y hY_meas n i ω ∂P
        = ∫ ω, Y i.1 ω / Real.sqrt (n + 1 : ℝ) ∂P := by
            rfl
      _ = (∫ ω, Y i.1 ω ∂P) / Real.sqrt (n + 1 : ℝ) := by
            rw [integral_div]
      _ = 0 := by simp [hYi_mean]

/-- Helper for Example 15.42: each standardized entry has the common variance scaled by
`(n + 1)⁻¹`. -/
lemma iidStandardizedArray_entryVariance
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (n : ℕ) (i : Fin (n + 1)) :
    Var[iid_standardized_array Y hY_meas n i; P] = Var[Y 0; P] / (n + 1 : ℝ) := by
  have hsqrt : Real.sqrt (n + 1 : ℝ) ≠ 0 := by
    positivity
  have hsq : (Real.sqrt (n + 1 : ℝ)) ^ 2 = (n + 1 : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  -- Rewrite the entry as a scalar multiple and use variance scaling plus identical distribution.
  calc
    Var[iid_standardized_array Y hY_meas n i; P]
        = Var[Y i.1; P] * (Real.sqrt (n + 1 : ℝ))⁻¹ ^ 2 := by
            rw [show (iid_standardized_array Y hY_meas n i) =
                fun ω ↦ Y i.1 ω * (Real.sqrt (n + 1 : ℝ))⁻¹ by
                  ext ω
                  simp [iid_standardized_array_apply, div_eq_mul_inv]]
            rw [variance_mul_const]
    _ = Var[Y i.1; P] / (n + 1 : ℝ) := by
          rw [div_eq_mul_inv, inv_pow, hsq]
    _ = Var[Y 0; P] / (n + 1 : ℝ) := by
          rw [(hY_ident i.1).variance_eq]

-- Proof sketch: identical distribution gives each row entry the variance of `Y 0` scaled by
-- `(n + 1)⁻¹`, so the row-variance sum is `1`.
/-- The standardized i.i.d. triangular array is normed when the common variance is `1`. -/
theorem iid_standardized_array_isNormed
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_var : Var[Y 0; P] = 1) :
    IsNormed (iid_standardized_array Y hY_meas) P := by
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    refine memLp_two_of_variance_ne_zero (hY_meas 0).aestronglyMeasurable ?_
    linarith
  refine ⟨?_, ?_⟩
  · intro n i
    have hYi_memLp_two : MemLp (Y i.1) 2 P := (hY_ident i.1).memLp_iff.2 hY0_memLp_two
    simpa [iid_standardized_array_apply, div_eq_mul_inv] using
      hYi_memLp_two.mul_const ((Real.sqrt (n + 1 : ℝ))⁻¹)
  · intro n
    -- Sum the constant entry variances across the `n + 1` coordinates.
    calc
      ∑ i : Fin ((iid_standardized_array Y hY_meas).rowLength n),
          Var[iid_standardized_array Y hY_meas n i; P]
        = ∑ i : Fin (n + 1), Var[Y 0; P] / (n + 1 : ℝ) := by
            refine Finset.sum_congr rfl fun i _ ↦ ?_
            simpa [iid_standardized_array] using
              iidStandardizedArray_entryVariance (Y := Y) (hY_meas := hY_meas)
                (P := P) hY_ident n i
      _ = (n + 1 : ℝ) * (Var[Y 0; P] / (n + 1 : ℝ)) := by
            simp
      _ = 1 := by
            have hn : (n + 1 : ℝ) ≠ 0 := by positivity
            rw [hY_var]
            field_simp [hn]

/-- Helper for Example 15.42: each standardized row sum has the common variance of `Y 0`. -/
lemma iidStandardizedArray_rowSumVariance
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY0_memLp_two : MemLp (Y 0) 2 P)
    (n : ℕ) :
    Var[(iid_standardized_array Y hY_meas).rowSum n; P] = Var[Y 0; P] := by
  let A := iid_standardized_array Y hY_meas
  have hA_indep : IsIndependent A P := iid_standardized_array_isIndependent
    (Y := Y) (hY_meas := hY_meas) (P := P) hY_indep
  have hA_memLp_two : ∀ i : Fin (A.rowLength n), MemLp (A n i) 2 P := by
    intro i
    have hYi_memLp_two : MemLp (Y i.1) 2 P := (hY_ident i.1).memLp_iff.2 hY0_memLp_two
    simpa [A, iid_standardized_array_apply, div_eq_mul_inv] using
      hYi_memLp_two.mul_const ((Real.sqrt (n + 1 : ℝ))⁻¹)
  have hPairwise :
      Set.Pairwise (↑(Finset.univ : Finset (Fin (A.rowLength n))))
        (fun i j ↦ A n i ⟂ᵢ[P] A n j) := by
    intro i _ j _ hij
    exact (hA_indep.rowwise n).indepFun hij
  calc
    Var[A.rowSum n; P] = ∑ i : Fin (A.rowLength n), Var[A n i; P] := by
      simpa [RealRandomVariableArray.rowSum] using
        ProbabilityTheory.IndepFun.variance_sum
          (μ := P) (X := fun i : Fin (A.rowLength n) ↦ A n i) (s := Finset.univ)
          (hs := fun i _ ↦ hA_memLp_two i) hPairwise
    _ = ∑ i : Fin (n + 1), Var[Y 0; P] / (n + 1 : ℝ) := by
          refine Finset.sum_congr rfl fun i _ ↦ ?_
          simpa [A] using
            iidStandardizedArray_entryVariance (Y := Y) (hY_meas := hY_meas)
              (P := P) hY_ident n i
    _ = (n + 1 : ℝ) * (Var[Y 0; P] / (n + 1 : ℝ)) := by simp
    _ = Var[Y 0; P] := by
          have hn : (n + 1 : ℝ) ≠ 0 := by positivity
          field_simp [hn]

/-- Helper for Example 15.42: multiplying the standardized `(2 + δ)`-moment of one entry by the
row length leaves the common `(2 + δ)`-moment scaled by `(n + 1)^(-δ / 2)`. -/
lemma standardizedEntryMomentScale
    {δ : ℝ} (n : ℕ) (x : ℝ) :
    (n + 1 : ℝ) * Real.rpow |x / Real.sqrt (n + 1 : ℝ)| (2 + δ) =
      (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |x| (2 + δ) := by
  let s : ℝ := Real.sqrt (n + 1 : ℝ)
  have hs : 0 < s := by
    dsimp [s]
    positivity
  have hsq : (n + 1 : ℝ) = s ^ 2 := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hdiv :
      Real.rpow (|x| / s) (2 + δ) = Real.rpow |x| (2 + δ) / Real.rpow s (2 + δ) := by
    simpa using (Real.div_rpow (abs_nonneg x) hs.le (2 + δ))
  have hsub :
      (s : ℝ) ^ (2 : ℝ) / s ^ (2 + δ) = s ^ (-δ) := by
    calc
      (s : ℝ) ^ (2 : ℝ) / s ^ (2 + δ) = s ^ (2 - (2 + δ)) := by
        simpa using (Real.rpow_sub hs 2 (2 + δ)).symm
      _ = s ^ (-δ) := by
        congr 1
        ring
  have hs_neg : Real.rpow s (-δ) = (n + 1 : ℝ) ^ (-δ / 2) := by
    have hs_sq_rpow : Real.rpow s 2 = (n + 1 : ℝ) := by
      simp [hsq]
    calc
      Real.rpow s (-δ) = Real.rpow s (2 * (-δ / 2)) := by
        congr 1
        ring
      _ = (Real.rpow s 2) ^ (-δ / 2) := by
        simpa using (Real.rpow_mul hs.le (2 : ℝ) (-δ / 2))
      _ = (n + 1 : ℝ) ^ (-δ / 2) := by rw [hs_sq_rpow]
  calc
    (n + 1 : ℝ) * Real.rpow |x / s| (2 + δ)
      = s ^ 2 * Real.rpow (|x| / s) (2 + δ) := by
          simp [hsq, abs_div, abs_of_pos hs]
    _ = s ^ 2 * (Real.rpow |x| (2 + δ) / Real.rpow s (2 + δ)) := by
          rw [hdiv]
    _ = (s ^ (2 : ℝ) / Real.rpow s (2 + δ)) * Real.rpow |x| (2 + δ) := by
          rw [← Real.rpow_natCast]
          ring
    _ = Real.rpow s (-δ) * Real.rpow |x| (2 + δ) := by
          exact congrArg (fun t : ℝ => t * Real.rpow |x| (2 + δ)) hsub
    _ = (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |x| (2 + δ) := by
          rw [hs_neg]

-- Proof sketch: the tail event for any row entry is `|Y i| > ε √(n + 1)`; by identical
-- distribution this does not depend on `i`, and the threshold tends to infinity with `n`.
/-- The standardized i.i.d. triangular array is null when the common law is centered. -/
theorem iid_standardized_array_isNull
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) :
    IsNull (iid_standardized_array Y hY_meas) P := by
  let A := iid_standardized_array Y hY_meas
  refine
    { toIsCentered := iid_standardized_array_isCentered (Y := Y) (hY_meas := hY_meas)
        (P := P) hY_ident hY_centered
      asymptotically_negligible := ?_ }
  intro ε hε
  let S : ℕ → Set Ω := fun n ↦ {ω | ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)|}
  have hS_meas : ∀ n, MeasurableSet (S n) := by
    intro n
    dsimp [S]
    measurability
  have htail_zero : Tendsto (fun n ↦ P (S n)) atTop (nhds 0) := by
    have hCastSucc : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add] using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hlim : ∀ ω, ∀ᶠ n in atTop, ω ∈ S n ↔ ω ∈ (∅ : Set Ω) := by
      intro ω
      have hsqrt :
          Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℝ)) atTop atTop := by
        exact Real.tendsto_sqrt_atTop.comp hCastSucc
      have hinv :
          Tendsto (fun n : ℕ ↦ (Real.sqrt (n + 1 : ℝ))⁻¹) atTop (nhds 0) := by
        simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt
      have hscaled :
          Tendsto (fun n : ℕ ↦ Y 0 ω / Real.sqrt (n + 1 : ℝ)) atTop (nhds 0) := by
        simpa [div_eq_mul_inv, mul_comm] using hinv.mul_const (Y 0 ω)
      have hsmall :
          ∀ᶠ n : ℕ in atTop, Y 0 ω / Real.sqrt (n + 1 : ℝ) ∈ Set.Ioo (-ε) ε := by
        have hneg : -ε < (0 : ℝ) := by linarith
        exact hscaled.eventually (Ioo_mem_nhds hneg hε)
      filter_upwards [hsmall] with n hn
      have hnot : ¬ ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)| := by
        have habs : |Y 0 ω / Real.sqrt (n + 1 : ℝ)| < ε := by
          simpa [Set.mem_Ioo, abs_lt] using hn
        exact not_lt.mpr habs.le
      simp [S, hnot]
    simpa using
      MeasureTheory.tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (L := atTop) (μ := P) (As := S) (A := (∅ : Set Ω)) hS_meas hlim
  have hsup_eq :
      (fun n ↦ ⨆ i : Fin (A.rowLength n), P {ω | ε < |A n i ω|}) = fun n ↦ P (S n) := by
    funext n
    change (⨆ i : Fin (n + 1), P {ω | ε < |A n i ω|}) = P (S n)
    have hterm :
        ∀ i : Fin (n + 1), P {ω | ε < |A n i ω|} = P (S n) := by
      intro i
      have hident :
          IdentDistrib (fun ω ↦ A n i ω)
            (fun ω ↦ Y 0 ω / Real.sqrt (n + 1 : ℝ)) P P := by
        simpa [A, iid_standardized_array_apply] using
          (hY_ident i.1).div_const (Real.sqrt (n + 1 : ℝ))
      have habs :
          IdentDistrib (fun ω ↦ |A n i ω|)
            (fun ω ↦ |Y 0 ω / Real.sqrt (n + 1 : ℝ)|) P P := by
        exact hident.comp measurable_abs
      simpa [A, S, iid_standardized_array_apply] using
        habs.measure_mem_eq measurableSet_Ioi
    simp [hterm]
  change Tendsto (fun n ↦ ⨆ i : Fin (A.rowLength n), P {ω | ε < |A n i ω|}) atTop (nhds 0)
  simpa [hsup_eq] using htail_zero

-- Proof sketch: independence identifies `Var[Sₙ]` with the sum of the row variances, so for the
-- standardized array the owner `lindebergFunction` is the truncated second moment of `Y 0`
-- outside the threshold `ε √(n + 1)`; identical distribution then reduces the row sum to a single
-- common term, which tends to `0`.
/-- The standardized triangular array attached to an i.i.d. sequence satisfies the chapter owner's
Lindeberg condition. -/
theorem iid_standardized_array_lindeberg
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P)
    (hY_var : Var[Y 0; P] = 1) :
    SatisfiesLindebergCondition (iid_standardized_array Y hY_meas) P := by
  let A := iid_standardized_array Y hY_meas
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    refine memLp_two_of_variance_ne_zero (hY_meas 0).aestronglyMeasurable ?_
    linarith
  refine
    { toIsCentered := iid_standardized_array_isCentered (Y := Y) (hY_meas := hY_meas)
        (P := P) hY_ident hY_centered
      memLp_two := ?_
      lindeberg_tendsto := ?_ }
  · intro n i
    have hYi_memLp_two : MemLp (Y i.1) 2 P := (hY_ident i.1).memLp_iff.2 hY0_memLp_two
    simpa [A, iid_standardized_array_apply, div_eq_mul_inv] using
      hYi_memLp_two.mul_const ((Real.sqrt (n + 1 : ℝ))⁻¹)
  · intro ε hε
    -- Route correction: avoid the later Theorem 15.43 shortcut and compute the owner
    -- `lindebergFunction` directly from Definition 15.40.
    have hSq_integrable : Integrable (fun ω ↦ (Y 0 ω) ^ 2) P := hY0_memLp_two.integrable_sq
    have hrowVar : ∀ n, Var[A.rowSum n; P] = 1 := by
      intro n
      simpa [hY_var] using
        iidStandardizedArray_rowSumVariance (Y := Y) (hY_meas := hY_meas)
          (P := P) hY_indep hY_ident hY0_memLp_two n
    let F : ℕ → Ω → ℝ := fun n ω ↦
      (n + 1 : ℝ) *
        Set.indicator {ω | ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)|}
          (fun ω ↦ (Y 0 ω / Real.sqrt (n + 1 : ℝ)) ^ 2) ω
    have hrow_eq : ∀ n, A.lindebergFunction P ε n = ∫ ω, F n ω ∂P := by
      intro n
      let J : ℝ := ∫ ω,
        Set.indicator {ω | ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)|}
          (fun ω ↦ (Y 0 ω / Real.sqrt (n + 1 : ℝ)) ^ 2) ω ∂P
      have hterm :
          ∀ i : Fin (n + 1),
            ∫ ω,
                Set.indicator
                  {ω | ε ^ 2 * Var[A.rowSum n; P] < (A n i ω) ^ 2}
                  (fun ω ↦ (A n i ω) ^ 2) ω ∂P = J := by
        intro i
        let g : ℝ → ℝ := fun x ↦ Set.indicator {x : ℝ | ε < |x|} (fun x ↦ x ^ 2) x
        have hg : Measurable g := by
          refine (measurable_id.pow_const 2).indicator ?_
          measurability
        have hident :
            IdentDistrib (fun ω ↦ A n i ω)
              (fun ω ↦ Y 0 ω / Real.sqrt (n + 1 : ℝ)) P P := by
          simpa [A, iid_standardized_array_apply] using
            (hY_ident i.1).div_const (Real.sqrt (n + 1 : ℝ))
        calc
          ∫ ω,
              Set.indicator
                {ω | ε ^ 2 * Var[A.rowSum n; P] < (A n i ω) ^ 2}
                (fun ω ↦ (A n i ω) ^ 2) ω ∂P
            = ∫ ω, g (A n i ω) ∂P := by
                congr 1 with ω
                rw [hrowVar n]
                by_cases hω : ε < |A n i ω|
                · have hsq : ε ^ 2 < (A n i ω) ^ 2 := by
                    have habs_sq : ε ^ 2 < |A n i ω| ^ 2 := by
                      nlinarith [hε, abs_nonneg (A n i ω), hω]
                    simpa [sq_abs] using habs_sq
                  simp [g, hω, hsq]
                · have hsq : ¬ ε ^ 2 < (A n i ω) ^ 2 := by
                    intro hsq
                    have habs_sq : ε ^ 2 < |A n i ω| ^ 2 := by
                      simpa [sq_abs] using hsq
                    have : ε < |A n i ω| := by
                      nlinarith [hε, abs_nonneg (A n i ω), habs_sq]
                    exact hω this
                  simp [g, hω, hsq]
          _ = ∫ ω, g (Y 0 ω / Real.sqrt (n + 1 : ℝ)) ∂P := by
                simpa [Function.comp] using (hident.comp hg).integral_eq
          _ = J := by rfl
      calc
        A.lindebergFunction P ε n
          = (Var[A.rowSum n; P])⁻¹ *
              ∑ i : Fin (A.rowLength n),
                ∫ ω,
                  Set.indicator
                    {ω | ε ^ 2 * Var[A.rowSum n; P] < (A n i ω) ^ 2}
                    (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
              rw [RealRandomVariableArray.lindebergFunction_def]
        _ = ∑ i : Fin (n + 1), J := by
              rw [hrowVar n]
              have hsum_eq :
                  ∑ i : Fin (n + 1),
                    ∫ ω,
                      Set.indicator
                        {ω | ε ^ 2 < (A n i ω) ^ 2}
                        (fun ω ↦ (A n i ω) ^ 2) ω ∂P =
                      ∑ i : Fin (n + 1), J := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    simpa [hrowVar n] using hterm i
              have hsum_eq' :
                  ∑ i : Fin (n + 1),
                    ∫ ω,
                      Set.indicator
                        {ω | ε ^ 2 * 1 < (A n i ω) ^ 2}
                        (fun ω ↦ (A n i ω) ^ 2) ω ∂P =
                      ∑ i : Fin (n + 1), J := by
                    simpa using hsum_eq
              calc
                1⁻¹ *
                    ∑ i : Fin (n + 1),
                      ∫ ω,
                        Set.indicator
                          {ω | ε ^ 2 * 1 < (A n i ω) ^ 2}
                          (fun ω ↦ (A n i ω) ^ 2) ω ∂P
                  = ∑ i : Fin (n + 1),
                      ∫ ω,
                        Set.indicator
                          {ω | ε ^ 2 * 1 < (A n i ω) ^ 2}
                          (fun ω ↦ (A n i ω) ^ 2) ω ∂P := by
                            simp
                _ = ∑ i : Fin (n + 1), J := hsum_eq'
        _ = (n + 1 : ℝ) * J := by simp
        _ = ∫ ω, F n ω ∂P := by
              simp [F, J, integral_const_mul]
    have hF_meas : ∀ n, AEStronglyMeasurable (F n) P := by
      intro n
      have hbase :
          Measurable
            (fun ω ↦
              Set.indicator {ω | ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)|}
                (fun ω ↦ (Y 0 ω / Real.sqrt (n + 1 : ℝ)) ^ 2) ω) := by
        refine (((hY_meas 0).div_const _).pow_const 2).indicator ?_
        measurability
      exact (hbase.const_mul (n + 1 : ℝ)).aestronglyMeasurable
    have hF_bound : ∀ n, ∀ᵐ ω ∂P, ‖F n ω‖ ≤ (Y 0 ω) ^ 2 := by
      intro n
      let s : ℝ := Real.sqrt (n + 1 : ℝ)
      have hs : 0 < s := by
        dsimp [s]
        positivity
      have hsq : (n + 1 : ℝ) = s ^ 2 := by
        dsimp [s]
        rw [Real.sq_sqrt]
        positivity
      filter_upwards with ω
      by_cases hω : ε < |Y 0 ω / s|
      · have hFsq : F n ω = (Y 0 ω) ^ 2 := by
          calc
            F n ω = (n + 1 : ℝ) * (Y 0 ω / s) ^ 2 := by
              simp [F, s, hω]
            _ = s ^ 2 * (Y 0 ω / s) ^ 2 := by rw [hsq]
            _ = (s * (Y 0 ω / s)) ^ 2 := by ring
            _ = (Y 0 ω) ^ 2 := by
                  congr 1
                  field_simp [hs.ne']
        simp [hFsq]
      · have hFzero : F n ω = 0 := by
          simp [F, s, hω]
        simpa [hFzero, sq_nonneg] using
          (show (0 : ℝ) ≤ (Y 0 ω) ^ 2 by exact sq_nonneg _)
    have hF_lim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ F n ω) atTop (nhds 0) := by
      have hCastSucc : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
        simpa [Nat.cast_add] using
          tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
      filter_upwards with ω
      have hsqrt :
          Tendsto (fun n : ℕ ↦ Real.sqrt (n + 1 : ℝ)) atTop atTop := by
        exact Real.tendsto_sqrt_atTop.comp hCastSucc
      have hinv :
          Tendsto (fun n : ℕ ↦ (Real.sqrt (n + 1 : ℝ))⁻¹) atTop (nhds 0) := by
        simpa [one_div] using tendsto_inv_atTop_zero.comp hsqrt
      have hscaled :
          Tendsto (fun n : ℕ ↦ Y 0 ω / Real.sqrt (n + 1 : ℝ)) atTop (nhds 0) := by
        simpa [div_eq_mul_inv, mul_comm] using hinv.mul_const (Y 0 ω)
      have hEq : (fun n ↦ F n ω) =ᶠ[atTop] fun _ ↦ 0 := by
        have hsmall :
            ∀ᶠ n : ℕ in atTop, Y 0 ω / Real.sqrt (n + 1 : ℝ) ∈ Set.Ioo (-ε) ε := by
          have hneg : -ε < (0 : ℝ) := by linarith
          exact hscaled.eventually (Ioo_mem_nhds hneg hε)
        filter_upwards [hsmall] with n hn
        have hnot : ¬ ε < |Y 0 ω / Real.sqrt (n + 1 : ℝ)| := by
          have habs : |Y 0 ω / Real.sqrt (n + 1 : ℝ)| < ε := by
            simpa [Set.mem_Ioo, abs_lt] using hn
          exact not_lt.mpr habs.le
        simp [F, hnot]
      exact tendsto_const_nhds.congr' hEq.symm
    have hF_tendsto : Tendsto (fun n ↦ ∫ ω, F n ω ∂P) atTop (nhds 0) := by
      simpa [F] using
        MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (fun ω ↦ (Y 0 ω) ^ 2)
          (Eventually.of_forall hF_meas)
          (Eventually.of_forall hF_bound)
          hSq_integrable hF_lim
    have hSeqEq :
        (fun n ↦ A.lindebergFunction P ε n) = fun n ↦ ∫ ω, F n ω ∂P := by
      funext n
      exact hrow_eq n
    change Tendsto (fun n ↦ A.lindebergFunction P ε n) atTop (nhds 0)
    simpa [hSeqEq] using hF_tendsto

-- Proof sketch: independence again identifies the owner denominator through
-- `Var[(iid_standardized_array Y hY_meas).rowSum n; P]`, and identical distribution reduces the
-- numerator to `(n + 1) ^ (-δ / 2)` times the common `(2 + δ)`-moment of `Y 0`, which tends to
-- `0`.
/-- Example 15.42: if an i.i.d. sequence has a finite common `(2 + δ)`-moment for some `δ > 0`,
then its standardized triangular array satisfies the chapter owner's Lyapunov condition. -/
theorem iid_standardized_array_lyapunov
    (hY_indep : iIndepFun Y P)
    (hY_ident : ∀ j, IdentDistrib (Y j) (Y 0) P P)
    (hY_centered : _root_.IsCentered (Y 0) P) {δ : ℝ} (hδ : 0 < δ)
    (hY_moment : Integrable (fun ω ↦ Real.rpow |Y 0 ω| (2 + δ)) P) :
    SatisfiesLyapunovCondition (iid_standardized_array Y hY_meas) P := by
  let A := iid_standardized_array Y hY_meas
  have hp_pos : 0 < 2 + δ := by linarith
  have hp_nonneg : 0 ≤ 2 + δ := by linarith
  have hp_ne_zero : ENNReal.ofReal (2 + δ) ≠ 0 := by
    intro hzero
    have : 2 + δ ≤ 0 := by
      simpa [ENNReal.ofReal_eq_zero] using hzero
    linarith
  have hY0_moment_memLp : MemLp (Y 0) (ENNReal.ofReal (2 + δ)) P := by
    have hMoment_norm :
        Integrable (fun ω ↦ ‖Y 0 ω‖ ^ (ENNReal.ofReal (2 + δ)).toReal) P := by
      simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_nonneg] using hY_moment
    exact
      (integrable_norm_rpow_iff (μ := P) (f := Y 0)
        (p := ENNReal.ofReal (2 + δ)) (hY_meas 0).aestronglyMeasurable hp_ne_zero
        ENNReal.ofReal_ne_top).1 hMoment_norm
  have hY0_memLp_two : MemLp (Y 0) 2 P := by
    refine hY0_moment_memLp.mono_exponent ?_
    simpa using ENNReal.ofReal_le_ofReal (show (2 : ℝ) ≤ 2 + δ by linarith)
  have hMoment_memLp :
      ∀ n i, MemLp (A n i) (ENNReal.ofReal (2 + δ)) P := by
    intro n i
    have hYi_memLp :
        MemLp (Y i.1) (ENNReal.ofReal (2 + δ)) P := (hY_ident i.1).memLp_iff.2 hY0_moment_memLp
    simpa [A, iid_standardized_array_apply, div_eq_mul_inv] using
      hYi_memLp.mul_const ((Real.sqrt (n + 1 : ℝ))⁻¹)
  have hMoment_tendsto :
      Tendsto
        (fun n : ℕ ↦
          ENNReal.ofReal
            (∫ ω, (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ) ∂P))
        atTop (nhds 0) := by
    let H : ℕ → Ω → ℝ := fun n ω ↦
      (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ)
    have hCastSucc : Tendsto (fun n : ℕ ↦ (n + 1 : ℝ)) atTop atTop := by
      simpa [Nat.cast_add] using
        tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    have hFactor_tendsto :
        Tendsto (fun n : ℕ ↦ (n + 1 : ℝ) ^ (-δ / 2)) atTop (nhds 0) := by
      simpa [Function.comp, neg_div] using
        (tendsto_rpow_neg_atTop (by positivity : 0 < δ / 2)).comp hCastSucc
    have hH_meas : ∀ n, AEStronglyMeasurable (H n) P := by
      intro n
      exact hY_moment.aestronglyMeasurable.const_mul ((n + 1 : ℝ) ^ (-δ / 2))
    have hH_bound :
        ∀ n, ∀ᵐ ω ∂P, ‖H n ω‖ ≤ Real.rpow |Y 0 ω| (2 + δ) := by
      intro n
      have hFactor_nonneg : 0 ≤ (n + 1 : ℝ) ^ (-δ / 2) := by
        exact Real.rpow_nonneg (by positivity : 0 ≤ (n + 1 : ℝ)) _
      have hFactor_le_one : (n + 1 : ℝ) ^ (-δ / 2) ≤ 1 := by
        refine Real.rpow_le_one_of_one_le_of_nonpos ?_ ?_
        · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
        · linarith
      filter_upwards with ω
      have hMoment_nonneg : 0 ≤ Real.rpow |Y 0 ω| (2 + δ) := by
        exact Real.rpow_nonneg (abs_nonneg (Y 0 ω)) _
      calc
        ‖H n ω‖ = (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ) := by
          rw [show ‖H n ω‖ =
              |(n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ)| by rfl]
          rw [abs_mul, abs_of_nonneg hFactor_nonneg, abs_of_nonneg hMoment_nonneg]
        _ ≤ 1 * Real.rpow |Y 0 ω| (2 + δ) := by
          gcongr
        _ = Real.rpow |Y 0 ω| (2 + δ) := by ring
    have hH_lim : ∀ᵐ ω ∂P, Tendsto (fun n ↦ H n ω) atTop (nhds 0) := by
      filter_upwards with ω
      simpa [H, zero_mul] using hFactor_tendsto.mul_const (Real.rpow |Y 0 ω| (2 + δ))
    have hIntegral_tendsto :
        Tendsto (fun n ↦ ∫ ω, H n ω ∂P) atTop (nhds 0) := by
      simpa [H] using
        MeasureTheory.tendsto_integral_filter_of_dominated_convergence
          (fun ω ↦ Real.rpow |Y 0 ω| (2 + δ))
          (Eventually.of_forall hH_meas)
          (Eventually.of_forall hH_bound)
          hY_moment hH_lim
    simpa using ENNReal.tendsto_ofReal hIntegral_tendsto
  refine
    { toIsCentered := iid_standardized_array_isCentered (Y := Y) (hY_meas := hY_meas)
        (P := P) hY_ident hY_centered
      exists_delta := ?_ }
  refine ⟨δ, hδ, hMoment_memLp, ?_⟩
  -- Route correction: keep the theorem at the owner level and split only on whether the
  -- common variance vanishes.
  by_cases hVar0 : Var[Y 0; P] = 0
  · have hY0_ae_zero : Y 0 =ᵐ[P] 0 := by
      have hconst : Y 0 =ᵐ[P] fun _ ↦ P[Y 0] :=
        ae_eq_integral_of_variance_eq_zero hY0_memLp_two hVar0
      simpa [hY_centered.2] using hconst
    have hYi_ae_zero : ∀ j, Y j =ᵐ[P] 0 := by
      intro j
      have hzero_mem : ∀ᵐ ω ∂P, Y 0 ω ∈ ({0} : Set ℝ) := by
        simpa using hY0_ae_zero
      have hmem_zero : ∀ᵐ ω ∂P, Y j ω ∈ ({0} : Set ℝ) :=
        (hY_ident j).symm.ae_mem_snd (measurableSet_singleton (0 : ℝ)) hzero_mem
      simpa using hmem_zero
    have hentry_zero : ∀ n i, A n i =ᵐ[P] 0 := by
      intro n i
      filter_upwards [hYi_ae_zero i.1] with ω hω
      simp [A, iid_standardized_array_apply, hω]
    have hlyap_zero : ∀ n, A.lyapunovFunction P δ n = 0 := by
      intro n
      have hnumerator_zero :
          ∑ i : Fin (A.rowLength n),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P = 0 := by
        refine Finset.sum_eq_zero fun i _ ↦ ?_
        refine MeasureTheory.lintegral_eq_zero_of_ae_eq_zero ?_
        filter_upwards [hentry_zero n i] with ω hω
        simp [hω, hp_pos.ne']
      rw [RealRandomVariableArray.lyapunovFunction_def]
      rw [iidStandardizedArray_rowSumVariance (Y := Y) (hY_meas := hY_meas)
        (P := P) hY_indep hY_ident hY0_memLp_two n, hVar0, hnumerator_zero]
      simp
    change Tendsto (fun n ↦ A.lyapunovFunction P δ n) atTop (nhds 0)
    simp [hlyap_zero]
  · have hVar_pos : 0 < Var[Y 0; P] := by
      exact lt_of_le_of_ne (ProbabilityTheory.variance_nonneg _ _) (by simpa [eq_comm] using hVar0)
    let c : ENNReal := (ENNReal.ofReal (Real.rpow (Var[Y 0; P]) (1 + δ / 2)))⁻¹
    have hc_ne_top : c ≠ ⊤ := by
      apply ENNReal.inv_ne_top.2
      exact by
        simpa [Real.rpow_pos_of_pos hVar_pos]
    have hlyap_eq :
        ∀ n,
          A.lyapunovFunction P δ n =
            c *
              ENNReal.ofReal
                (∫ ω, (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ) ∂P) := by
      intro n
      let s : ℝ := Real.sqrt (n + 1 : ℝ)
      let J : ℝ := ∫ ω, Real.rpow |Y 0 ω / s| (2 + δ) ∂P
      have hs : 0 < s := by
        dsimp [s]
        positivity
      have hScaled_memLp :
          MemLp (fun ω ↦ Y 0 ω / s) (ENNReal.ofReal (2 + δ)) P := by
        simpa [s, div_eq_mul_inv] using hY0_moment_memLp.mul_const s⁻¹
      have hScaled_integrable :
          Integrable (fun ω ↦ Real.rpow |Y 0 ω / s| (2 + δ)) P := by
        simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_nonneg, J, s, abs_div,
          abs_of_pos hs] using
          hScaled_memLp.integrable_norm_rpow hp_ne_zero ENNReal.ofReal_ne_top
      have hScaled_nonneg :
          0 ≤ᵐ[P] fun ω ↦ Real.rpow |Y 0 ω / s| (2 + δ) := by
        filter_upwards with ω
        exact Real.rpow_nonneg (abs_nonneg (Y 0 ω / s)) _
      have hJ_nonneg : 0 ≤ J := by
        exact integral_nonneg fun _ ↦ Real.rpow_nonneg (abs_nonneg _) _
      have hpow_meas : Measurable (fun x : ℝ ↦ Real.rpow |x| (2 + δ)) := by
        exact (Real.continuous_rpow_const (by linarith : 0 ≤ 2 + δ)).measurable.comp measurable_abs
      have hterm :
          ∀ i : Fin (n + 1),
            ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P =
              ENNReal.ofReal J := by
        intro i
        have hentry_ident :
            IdentDistrib (fun ω ↦ A n i ω) (fun ω ↦ Y 0 ω / s) P P := by
          simpa [A, s, iid_standardized_array_apply] using (hY_ident i.1).div_const s
        have hMoment_ident :
            IdentDistrib
              (fun ω ↦ Real.rpow |A n i ω| (2 + δ))
              (fun ω ↦ Real.rpow |Y 0 ω / s| (2 + δ)) P P := by
          simpa [Function.comp] using hentry_ident.comp hpow_meas
        have hentry_integrable :
            Integrable (fun ω ↦ Real.rpow |A n i ω| (2 + δ)) P := by
          simpa [Real.norm_eq_abs, ENNReal.toReal_ofReal hp_nonneg] using
            (hMoment_memLp n i).integrable_norm_rpow hp_ne_zero ENNReal.ofReal_ne_top
        have hentry_nonneg :
            0 ≤ᵐ[P] fun ω ↦ Real.rpow |A n i ω| (2 + δ) := by
          filter_upwards with ω
          exact Real.rpow_nonneg (abs_nonneg (A n i ω)) _
        calc
          ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P
            = ENNReal.ofReal (∫ ω, Real.rpow |A n i ω| (2 + δ) ∂P) := by
                symm
                exact
                  MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                    hentry_integrable hentry_nonneg
          _ = ENNReal.ofReal J := by
                rw [show (∫ ω, Real.rpow |A n i ω| (2 + δ) ∂P) = J by
                  simpa [J] using hMoment_ident.integral_eq]
      have hrowVar :
          Var[A.rowSum n; P] = Var[Y 0; P] := iidStandardizedArray_rowSumVariance
            (Y := Y) (hY_meas := hY_meas) (P := P) hY_indep hY_ident hY0_memLp_two n
      calc
        A.lyapunovFunction P δ n
          = (ENNReal.ofReal (Real.rpow (Var[A.rowSum n; P]) (1 + δ / 2)))⁻¹ *
              ∑ i : Fin (A.rowLength n),
                ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P := by
                rw [RealRandomVariableArray.lyapunovFunction_def]
        _ = c * ∑ i : Fin (n + 1), ENNReal.ofReal J := by
              rw [hrowVar]
              have hsum_eq :
                  ∑ i : Fin (A.rowLength n),
                    ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P =
                      ∑ i : Fin (n + 1), ENNReal.ofReal J := by
                    refine Finset.sum_congr rfl fun i _ ↦ ?_
                    simpa [A] using hterm i
              calc
                (ENNReal.ofReal (Real.rpow (Var[Y 0; P]) (1 + δ / 2)))⁻¹ *
                    ∑ i : Fin (A.rowLength n),
                      ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P
                  = c *
                      ∑ i : Fin (A.rowLength n),
                        ∫⁻ ω, ENNReal.ofReal (Real.rpow |A n i ω| (2 + δ)) ∂P := by
                          rfl
                _ = c * ∑ i : Fin (n + 1), ENNReal.ofReal J := by
                      simpa [A] using congrArg (fun t ↦ c * t) hsum_eq
        _ = c * ((n + 1 : ENNReal) * ENNReal.ofReal J) := by simp
        _ = c * ENNReal.ofReal ((n + 1 : ℝ) * J) := by
              congr 1
              have hnat : (n + 1 : ENNReal) = ENNReal.ofReal (n + 1 : ℝ) := by
                simpa using (ENNReal.ofReal_natCast (n + 1)).symm
              rw [hnat]
              simpa [mul_comm] using
                (ENNReal.ofReal_mul (p := (n + 1 : ℝ)) (q := J)
                  (show 0 ≤ (n + 1 : ℝ) by positivity)).symm
        _ = c *
            ENNReal.ofReal
              (∫ ω, (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ) ∂P) := by
              congr 1
              congr 1
              dsimp [J]
              rw [← integral_const_mul]
              refine integral_congr_ae ?_
              filter_upwards with ω
              simpa [s] using
                standardizedEntryMomentScale (n := n) (δ := δ) (x := Y 0 ω)
    have hscaled_tendsto :
        Tendsto
          (fun n : ℕ ↦
            c *
              ENNReal.ofReal
                (∫ ω, (n + 1 : ℝ) ^ (-δ / 2) * Real.rpow |Y 0 ω| (2 + δ) ∂P))
          atTop (nhds 0) := by
      simpa [c] using ENNReal.Tendsto.const_mul (a := c) hMoment_tendsto (Or.inr hc_ne_top)
    change Tendsto (fun n ↦ A.lyapunovFunction P δ n) atTop (nhds 0)
    simpa [hlyap_eq] using hscaled_tendsto

end IIDStandardizedArray

end
