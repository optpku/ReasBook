/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Definition_10_3
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Example_10_2
import Books.ProbabilityTheory_Klenke_2020.Items.Chap10.Theorem_10_15

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

universe u

section

variable {Ω : Type u} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ} [SigmaFiniteFiltration μ ℱ]
variable {X : ℕ → Ω → ℝ} {τ : Ω → ℕ∞}

/- Lemma 11.13 is `source-facing` in the chapter's discrete-time square-variation theory. Its
owner abstraction is the canonical square variation `⟨X⟩[ℱ, μ]` from Definition 10.3, while
`IsSquareVariationProcess` is only the source-style witness view and the identity between the
predictable part of the stopped squared process and the stopped predictable part is the resulting
`bridge/view` consequence. -/

local notation "squareProcess" => fun n ω ↦ (X n ω) ^ 2
local notation "stoppedSquareProcess" => fun n ω ↦ (stoppedProcess X τ n ω) ^ 2

private theorem isPredictable_stoppedProcess {A : ℕ → Ω → ℝ}
    (hA : IsPredictable ℱ A) (hτ : IsStoppingTime ℱ τ) :
    IsPredictable ℱ (stoppedProcess A τ) := by
  refine isPredictable_of_measurable_add_one ?_ ?_
  · have hzero : stoppedProcess A τ 0 = A 0 := by
      ext ω
      simp [stoppedProcess]
    rw [hzero]
    exact (hA.adapted 0).measurable
  · intro n
    rw [stoppedProcess_eq (n + 1)]
    have hsum_fun :
        Measurable[ℱ n]
          (fun ω ↦ ∑ i ∈ Finset.range (n + 1), Set.indicator {a | τ a = i} (A i) ω) :=
      Finset.measurable_fun_sum (Finset.range (n + 1)) fun i hi ↦ by
        have hi' : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        exact Measurable.indicator (((hA.adapted i).measurable).le <| ℱ.mono hi')
          (hτ.measurableSet_eq_le hi')
    have hsum :
        Measurable[ℱ n] (∑ i ∈ Finset.range (n + 1), Set.indicator {a | τ a = i} (A i)) := by
      convert hsum_fun using 1
      ext ω
      simp [Finset.sum_apply]
    have hfirst :
        Measurable[ℱ n] (Set.indicator {a | n + 1 ≤ τ a} (A (n + 1))) :=
      Measurable.indicator (hA.measurable_add_one n) <| by
        have h_eq : {a | n + 1 ≤ τ a} = {a | n < τ a} := by
          ext ω
          cases hτω : τ ω with
          | top => simp [hτω]
          | coe k =>
              simp only [Set.mem_setOf_eq, hτω, Nat.cast_lt]
              exact_mod_cast (Nat.lt_iff_add_one_le.symm : n + 1 ≤ k ↔ n < k)
        rw [h_eq]
        exact hτ.measurableSet_gt n
    have hadd :
        Measurable[ℱ n]
          (Set.indicator {a | n + 1 ≤ τ a} (A (n + 1)) +
            ∑ i ∈ Finset.range (n + 1), Set.indicator {a | τ a = i} (A i)) :=
      hfirst.add hsum
    exact hadd

private lemma stoppedProcess_succ_sub_eq_indicator
    (τ : Ω → ℕ∞) (f : ℕ → Ω → ℝ) (n : ℕ) :
    stoppedProcess f τ (n + 1) - stoppedProcess f τ n =
      Set.indicator {ω | τ ω ≤ n}ᶜ (f (n + 1) - f n) := by
  ext ω
  by_cases h : τ ω ≤ n
  · have h' : τ ω ≤ n + 1 := h.trans (by exact_mod_cast Nat.le_succ n)
    simp [stoppedProcess_eq_of_ge h, stoppedProcess_eq_of_ge h', h]
  · have h' : (n + 1 : ℕ∞) ≤ τ ω := by
      cases hτω : τ ω with
      | top => simp
      | coe a =>
          have hn : ¬ a ≤ n := by simpa [hτω] using h
          have : n < a := lt_of_not_ge hn
          exact_mod_cast Nat.succ_le_of_lt this
    have hn : (n : ℕ∞) ≤ τ ω := by
      exact le_trans (by exact_mod_cast Nat.le_succ n) h'
    simp [stoppedProcess_eq_of_le hn, stoppedProcess_eq_of_le h', h]

omit [SigmaFiniteFiltration μ ℱ] in
private theorem stoppedProcess_predictablePart_ae_eq {Y : ℕ → Ω → ℝ}
    (hY : ∀ n, Integrable (Y n) μ) (hτ : IsStoppingTime ℱ τ) :
    ∀ n, predictablePart (stoppedProcess Y τ) ℱ μ n =ᵐ[μ]
      stoppedProcess (predictablePart Y ℱ μ) τ n := by
  intro n
  induction n with
  | zero =>
      filter_upwards [] with ω
      simp [predictablePart, stoppedProcess]
  | succ n ih =>
      have hcond :
          μ[stoppedProcess Y τ (n + 1) - stoppedProcess Y τ n | ℱ n] =ᵐ[μ]
            Set.indicator {ω | τ ω ≤ n}ᶜ (μ[Y (n + 1) - Y n | ℱ n]) := by
        rw [stoppedProcess_succ_sub_eq_indicator τ Y n]
        exact condExp_indicator ((hY (n + 1)).sub (hY n)) ((hτ.measurableSet_le n).compl)
      calc
        predictablePart (stoppedProcess Y τ) ℱ μ (n + 1)
            = predictablePart (stoppedProcess Y τ) ℱ μ n +
                μ[stoppedProcess Y τ (n + 1) - stoppedProcess Y τ n | ℱ n] := by
                  simp [predictablePart, Finset.sum_range_succ]
        _ =ᵐ[μ] stoppedProcess (predictablePart Y ℱ μ) τ n +
              Set.indicator {ω | τ ω ≤ n}ᶜ (μ[Y (n + 1) - Y n | ℱ n]) := by
              simpa using ih.add hcond
        _ = stoppedProcess (predictablePart Y ℱ μ) τ n +
              Set.indicator {ω | τ ω ≤ n}ᶜ
                (predictablePart Y ℱ μ (n + 1) - predictablePart Y ℱ μ n) := by
              congr 2
              ext ω
              simp [predictablePart, Finset.sum_range_succ]
        _ = stoppedProcess (predictablePart Y ℱ μ) τ (n + 1) := by
              ext ω
              have hω := congrFun
                (stoppedProcess_succ_sub_eq_indicator τ (predictablePart Y ℱ μ) n) ω
              have hω' := sub_eq_iff_eq_add.mp hω
              simpa [add_comm] using hω'.symm

-- Proof sketch: expand `predictablePart` one step at a time, identify the stopped squared
-- increment with an indicator of the unstopped squared increment, pull that indicator through the
-- conditional expectation because `{τ ≤ n}ᶜ ∈ ℱ n`, and compare the resulting increment formula
-- with the corresponding increment formula for the stopped predictable part.
/-- Lemma 11.13: if `X` is a square-integrable discrete-time martingale, then the stopped square
variation process `⟨X⟩^τ` is a square-variation process of the stopped martingale `X^τ`. -/
theorem stoppedProcess_sq_isSquareVariationProcess
    (hX : Martingale X ℱ μ)
    (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ) :
    ProbabilityTheory.IsSquareVariationProcess ℱ μ
      (stoppedProcess X τ) (stoppedProcess (⟨X⟩[ℱ, μ]) τ) := by
  refine ⟨?_, isPredictable_stoppedProcess squareVariation_predictable hτ, ?_⟩
  · ext ω
    simp [stoppedProcess]
  · have hM : Martingale (fun n ω ↦ X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω) ℱ μ :=
      square_sub_squareVariation_martingale hX hXsq
    have hStoppedM : Martingale (stoppedProcess (fun n ω ↦ X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω) τ) ℱ μ := by
      rw [martingale_iff]
      refine ⟨?_, hM.submartingale.stoppedProcess hτ⟩
      have hNegStopped : Submartingale (stoppedProcess (fun n ω ↦ -(X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω)) τ) ℱ μ :=
        hM.neg.submartingale.stoppedProcess hτ
      have hNegEq :
          -(stoppedProcess (fun n ω ↦ -(X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω)) τ) =
            stoppedProcess (fun n ω ↦ X n ω ^ 2 - (⟨X⟩[ℱ, μ]) n ω) τ := by
        funext n ω
        simp [stoppedProcess]
      simpa only [hNegEq] using hNegStopped.neg
    simpa [stoppedProcess] using hStoppedM

-- Companion bridge: the square variation process from Lemma 11.13 agrees timewise almost surely
-- with the canonical predictable part of the stopped squared process.
omit [SigmaFiniteFiltration μ ℱ] in
theorem stoppedProcess_predictablePart_sq_ae_eq
    (hXsq : ∀ n, Integrable (fun ω ↦ (X n ω) ^ 2) μ)
    (hτ : IsStoppingTime ℱ τ) :
    ∀ n, predictablePart stoppedSquareProcess ℱ μ n =ᵐ[μ] stoppedProcess (⟨X⟩[ℱ, μ]) τ n := by
  intro n
  change predictablePart (stoppedProcess squareProcess τ) ℱ μ n =ᵐ[μ]
    stoppedProcess (predictablePart squareProcess ℱ μ) τ n
  exact stoppedProcess_predictablePart_ae_eq hXsq hτ n

end
