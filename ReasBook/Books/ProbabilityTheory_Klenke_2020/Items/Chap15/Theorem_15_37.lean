/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped Topology NNReal

universe u

noncomputable section

/-- The standardized partial sum appearing in the central limit theorem, written with Lean's
`0`-based indexing for the i.i.d. sequence. -/
def standardizedPartialSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω ↦ (Real.sqrt (n * Var[X 0; P]))⁻¹ *
    (Finset.sum (Finset.range n) (fun k ↦ X k ω) - n * P[X 0])

-- Proof sketch: combine the `AEMeasurable` hypotheses for the summands, then use closure of
-- `AEMeasurable` under finite sums, subtraction of constants, and scalar multiplication.
/-- The standardized partial sums are measurable whenever the underlying sequence is measurable. -/
theorem aemeasurable_standardizedPartialSum {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ)
    (hX : ∀ n, AEMeasurable (X n) P) (n : ℕ) :
    AEMeasurable (standardizedPartialSum P X n) P := by
  -- Proof comment: `standardizedPartialSum` is a scalar multiple of a finite measurable sum minus
  -- a constant, so `AEMeasurable` follows from the closure properties of measurable functions.
  unfold standardizedPartialSum
  refine AEMeasurable.const_mul ?_ _
  refine (Finset.aemeasurable_fun_sum _ fun k _ ↦ hX k).sub ?_
  exact aemeasurable_const

/-- Helper for Theorem 15.37: the standard Gaussian assigns zero mass to the boundary of the real
preimage of an `EReal` closed interval. -/
private lemma standardGaussian_nullBoundary_preimageIcc {a b : EReal} (hab : a < b) :
    (gaussianReal 0 1) (frontier (((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)) = 0 := by
  -- Proof comment: normalize the `EReal` interval to one of the standard real interval shapes and
  -- then use that a nondegenerate Gaussian has no atoms.
  have hNoAtoms : NoAtoms (gaussianReal 0 1) := by
    simpa using
      (ProbabilityTheory.noAtoms_gaussianReal (μ := 0) (v := (1 : NNReal)) one_ne_zero)
  rcases (EReal.exists (p := fun x => x = a)).mp ⟨a, rfl⟩ with rfl | rfl | ⟨a, rfl⟩
  · rcases (EReal.exists (p := fun x => x = b)).mp ⟨b, rfl⟩ with rfl | rfl | ⟨b, rfl⟩
    · exact (lt_irrefl (⊥ : EReal) hab).elim
    ·
      have hSet : (((↑) : ℝ → EReal) ⁻¹' Set.Icc (⊥ : EReal) (⊤ : EReal)) = Set.univ := by
        ext x
        simp
      rw [hSet]
      simp
    ·
      have hSet : (((↑) : ℝ → EReal) ⁻¹' Set.Icc (⊥ : EReal) b) = Set.Iic b := by
        ext x
        simp
      rw [hSet, frontier_Iic]
      simpa using (Set.finite_singleton b).measure_zero (gaussianReal 0 1)
  · exact ((not_lt_of_ge (le_top : b ≤ (⊤ : EReal))) hab).elim
  · rcases (EReal.exists (p := fun x => x = b)).mp ⟨b, rfl⟩ with rfl | rfl | ⟨b, rfl⟩
    · exact ((not_lt_of_ge (bot_le : (⊥ : EReal) ≤ (a : EReal))) hab).elim
    ·
      have hSet : (((↑) : ℝ → EReal) ⁻¹' Set.Icc a (⊤ : EReal)) = Set.Ici a := by
        ext x
        simp
      rw [hSet, frontier_Ici]
      simpa using (Set.finite_singleton a).measure_zero (gaussianReal 0 1)
    ·
      have hab' : a < b := by
        simpa using hab
      rw [EReal.preimage_coe_Icc, frontier_Icc hab'.le]
      simpa using (by simp : ({a, b} : Set ℝ).Finite).measure_zero (gaussianReal 0 1)

/-- Helper for Theorem 15.37: the standard Gaussian mass of the `EReal` interval preimage equals
the displayed density integral. -/
private lemma standardGaussian_measure_preimageIcc_eq_integral {a b : EReal} :
    ((gaussianReal 0 1 : Measure ℝ).real ((((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)) =
      ∫ x,
        Set.indicator ((((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)) (gaussianPDFReal 0 1) x ∂volume) := by
  let A : Set ℝ := ((↑) : ℝ → EReal) ⁻¹' Set.Icc a b
  have hA_meas : MeasurableSet A := by
    exact isClosed_Icc.measurableSet.preimage continuous_coe_real_ereal.measurable
  -- Proof comment: rewrite the Gaussian mass by its density formula and then identify the set
  -- integral with the corresponding indicator integral.
  change (gaussianReal 0 1 : Measure ℝ).real A =
    ∫ x, Set.indicator A (gaussianPDFReal 0 1) x ∂volume
  rw [measureReal_def, ProbabilityTheory.gaussianReal_apply_eq_integral (μ := 0) (v := (1 : NNReal))
    one_ne_zero A]
  rw [ENNReal.toReal_ofReal (integral_nonneg fun x ↦ gaussianPDFReal_nonneg 0 1 x)]
  simpa [A] using (integral_indicator (μ := volume) (f := gaussianPDFReal 0 1) hA_meas).symm

-- Proof sketch: apply the one-dimensional central limit theorem in mathlib to the centered sums
-- `(√n)⁻¹ (∑_{k < n} X k - n * P[X 0])`, then use the continuous mapping theorem for division by
-- `√(Var[X 0; P])` to identify the limit law as `gaussianReal 0 1`.
/-- Theorem 15.37 (1): the laws of the standardized partial sums converge weakly to the standard
Gaussian law. -/
theorem standardizedPartialSumLaw_tendsto_standardGaussian {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 P)
    (hVar : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n))
      atTop
      (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
  have mX0 := (hident 0).aemeasurable_fst
  have intX0 : Integrable (X 0) P := hX.integrable one_le_two
  have hrewrite (n : ℕ) (ω : Ω) :
      standardizedPartialSum P X n ω =
        (Real.sqrt n)⁻¹ *
          ∑ k ∈ Finset.range n, (X k ω - P[X 0]) / Real.sqrt (Var[X 0; P]) := by
    -- Proof comment: rewrite the variance normalization as the centered CLT normalization followed
    -- by division by `√(Var[X 0; P])`.
    rw [standardizedPartialSum, ← Finset.sum_div, Finset.sum_sub_distrib]
    simp [field]
  have hLaw : HasLaw id (gaussianReal 0 1) (gaussianReal 0 1) :=
    ProbabilityTheory.HasLaw.id
  have hCLT :
      TendstoInDistribution
        (fun (n : ℕ) ω ↦
          (Real.sqrt n)⁻¹ *
            ∑ k ∈ Finset.range n, (X k ω - P[X 0]) / Real.sqrt (Var[X 0; P]))
        atTop id (fun _ ↦ P) (gaussianReal 0 1) := by
    -- Proof comment: apply the canonical one-dimensional CLT to the centered, variance-one
    -- sequence `((X n - E[X₀]) / √Var[X₀])`.
    convert
      (ProbabilityTheory.tendstoInDistribution_inv_sqrt_mul_sum
        (P := P) (P' := gaussianReal 0 1)
        (X := fun n ω ↦ (X n ω - P[X 0]) / Real.sqrt (Var[X 0; P])) (Y := id) hLaw
        ?_ ?_ ?_ ?_) using 1
    · rw [integral_div, integral_sub intX0 (by simp)]
      simp
    · simp only [Pi.pow_apply, div_pow]
      rw [integral_div, ← variance_eq_integral mX0, Real.sq_sqrt (variance_nonneg _ _),
        div_self hVar]
    · exact hindep.comp (fun _ x ↦ (x - P[X 0]) / Real.sqrt (Var[X 0; P])) (by fun_prop)
    · convert fun n ↦
        (hident n).comp (u := fun x ↦ (x - P[X 0]) / Real.sqrt (Var[X 0; P])) (by fun_prop)
  have hStandardized :
      TendstoInDistribution (fun n ↦ standardizedPartialSum P X n) atTop id (fun _ ↦ P)
        (gaussianReal 0 1) := by
    -- Proof comment: replace the normalized CLT surface by the file-local definition
    -- `standardizedPartialSum`.
    refine TendstoInDistribution.congr (fun n ↦ ?_) (by simp) hCLT
    filter_upwards with ω
    exact (hrewrite n ω).symm
  -- Proof comment: the law-level statement is the `tendsto` field of the convergence-in-
  -- distribution statement.
  simpa using hStandardized.tendsto

-- Proof sketch: combine the weak convergence from part (1) with the portmanteau theorem for the
-- Borel set `((↑) : ℝ → EReal) ⁻¹' Set.Icc a b`, use absolute continuity of `gaussianReal 0 1`
-- to see that its boundary has measure zero, and then rewrite the limiting Gaussian mass as the
-- integral of the standard Gaussian density over that interval.
/-- Theorem 15.37 (2): for `-∞ ≤ a < b ≤ +∞`, the probabilities of the standardized partial sums
falling in the closed interval determined by `a` and `b` converge to the integral of the standard
Gaussian density over that interval. -/
theorem standardizedPartialSum_intervalProb_tendsto {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : ℕ → Ω → ℝ) (hX : MemLp (X 0) 2 P)
    (hVar : Var[X 0; P] ≠ 0) (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P) {a b : EReal} (hab : a < b) :
    Tendsto
      (fun n ↦
        ((ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n) :
            Measure ℝ).real (((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)))
      atTop
      (𝓝
        (∫ x, Set.indicator ((((↑) : ℝ → EReal) ⁻¹' Set.Icc a b)) (gaussianPDFReal 0 1) x
          ∂volume)) := by
  let A : Set ℝ := ((↑) : ℝ → EReal) ⁻¹' Set.Icc a b
  have hLaw :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n))
        atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) :=
    standardizedPartialSumLaw_tendsto_standardGaussian P X hX hVar hindep hident
  have hFrontier : (gaussianReal 0 1) (frontier A) = 0 := by
    -- Proof comment: the only boundary points are interval endpoints, and the Gaussian has no
    -- atoms there.
    simpa [A] using standardGaussian_nullBoundary_preimageIcc hab
  have hMass :
      Tendsto
        (fun n ↦
          ((ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n) :
            Measure ℝ) A))
        atTop
        (𝓝 ((gaussianReal 0 1 : Measure ℝ) A)) := by
    exact
      ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto'
        (E := A) hLaw hFrontier
  have hMassReal :
      Tendsto
        (fun n ↦
          ((ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P X (fun k ↦ (hident k).aemeasurable_fst) n) :
            Measure ℝ).real A))
        atTop
        (𝓝 ((gaussianReal 0 1 : Measure ℝ).real A)) := by
    -- Proof comment: real-valued interval masses are obtained by composing the `ENNReal` masses
    -- with `toReal`, which is continuous away from `∞`.
    simpa [measureReal_def] using
      (ENNReal.tendsto_toReal (measure_ne_top (gaussianReal 0 1) A)).comp hMass
  have hIntegral :
      ((gaussianReal 0 1 : Measure ℝ).real A) =
        ∫ x, Set.indicator A (gaussianPDFReal 0 1) x ∂volume := by
    -- Proof comment: identify the Gaussian limit mass with the displayed density integral.
    simpa [A] using standardGaussian_measure_preimageIcc_eq_integral (a := a) (b := b)
  -- Proof comment: portmanteau gives convergence of the interval masses, and the Gaussian mass is
  -- rewritten using its density.
  simpa [A] using hIntegral ▸ hMassReal
