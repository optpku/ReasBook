/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory Topology

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

noncomputable section

-- Proof sketch: unfold `standardizedPartialSum` for the shifted sequence `fun k ↦ X (k + 1)` and
-- rewrite the common mean and variance using `hμ` and `hσ2`.
/-- For the textbook sequence `X₁, X₂, …`, the chapter owner `standardizedPartialSum` is exactly
the CLT-normalized centered finite sum `(n σ²)^(-1/2) ∑_{k=1}^n (X_k - μ)`. -/
theorem standardizedPartialSum_succ_apply
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (μ σ2 : ℝ)
    (hμ : P[X 1] = μ) (hσ2 : Var[X 1; P] = σ2) (n : ℕ) (ω : Ω) :
    standardizedPartialSum P (fun k ↦ X (k + 1)) n ω =
      (Real.sqrt (n * σ2))⁻¹ * ∑ k ∈ Finset.range n, (X (k + 1) ω - μ) := by
  -- Rewrite the chapter owner formula using the textbook mean and variance at index `1`.
  rw [standardizedPartialSum]
  simp only [hμ, hσ2]
  -- Identify the centered finite sum with the difference of the raw sum and `n * μ`.
  congr 1
  rw [Finset.sum_sub_distrib]
  simp

-- Proof sketch: transfer Lemma 15.36 to the canonical pushforward law of
-- `standardizedPartialSum P (fun k ↦ X (k + 1)) n`. The companion theorem
-- `standardizedPartialSum_succ_apply` recovers the textbook `S_n^*` formula, while the owner
-- `ProbabilityMeasure.map` identifies the same law with the pushforward measure appearing below.
/-- Lemma 15.36: if `X₁, X₂, …` are i.i.d. real random variables with mean `μ` and variance
`σ² > 0`, then the characteristic functions of the normalized partial sums `S_n^*` converge
pointwise to the standard Gaussian characteristic function `t ↦ exp (-t² / 2)`. -/
theorem charFun_cltNormalizedPartialSum_tendsto_standardGaussian
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P)
    (hX_ident : ∀ n, IdentDistrib (X (n + 1)) (X 1) P P)
    (hVar : 0 < Var[X 1; P])
    (t : ℝ) :
    Tendsto
      (fun n : ℕ ↦
        charFun (P.map (standardizedPartialSum P (fun k ↦ X (k + 1)) n)) t)
      atTop (𝓝 (Complex.exp (-(t ^ 2 / 2 : ℝ)))) := by
  -- Positive variance gives the `L²` hypothesis required by the law-level CLT owner theorem.
  have hX_memLp : MemLp (X 1) 2 P := by
    refine memLp_two_of_variance_ne_zero (μ := P) (X := X 1)
      (hX_ident 0).aemeasurable_fst.aestronglyMeasurable ?_
    exact ne_of_gt hVar
  -- Route correction: instead of rebuilding the textbook Taylor expansion, reuse the existing
  -- weak convergence theorem for the shifted sequence `fun k ↦ X (k + 1)`.
  have hLaw :
      Tendsto
        (fun n ↦
          ProbabilityMeasure.map ⟨P, inferInstance⟩
            (aemeasurable_standardizedPartialSum P (fun k ↦ X (k + 1))
              (fun k ↦ (hX_ident k).aemeasurable_fst) n))
        atTop
        (𝓝 ((⟨gaussianReal 0 1, inferInstance⟩ : ProbabilityMeasure ℝ))) := by
    simpa using
      (standardizedPartialSumLaw_tendsto_standardGaussian
        (P := P) (X := fun k ↦ X (k + 1)) hX_memLp (ne_of_gt hVar) hX_indep hX_ident)
  -- Translate weak convergence of laws into pointwise convergence of characteristic functions.
  have hchar := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hLaw t
  -- Normalize the standard Gaussian characteristic function to the displayed exponent.
  simpa [charFun_gaussianReal, neg_div] using hchar
