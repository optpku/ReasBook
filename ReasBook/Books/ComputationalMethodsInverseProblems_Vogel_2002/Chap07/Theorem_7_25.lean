/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_15.Reconstruction
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.Benchmark
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_25.DiscrepancyChoice
public import Mathlib.Analysis.Asymptotics.Theta

public section

open scoped Asymptotics

namespace TsvdDiscrepancy

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- thm_7_25. Theorem 7.25 (Regularization Parameter Choice for the
Discrepancy Principle Applied to TSVD). Main labeled source-facing entry.

For a TSVD discrepancy-principle truncation family `mDiscrep` solving `(7.88)`,
assume the Chapter 7 semistochastic data model along a fixed sample `ω0` of a
noise field `η`, together with the white-noise moment hypotheses and the
algebraic singular-value/Fourier-coefficient decay assumptions used throughout
the TSVD analysis. Then `mDiscrep` is asymptotically equivalent to the explicit
benchmark sequence from `(7.89)`. -/
theorem isEquivalent_indexBenchmark
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (b c p q σ : ℝ)
    (η : ℕ → Ω → F) (ω0 : Ω) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mDiscrep : ℕ → ℕ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_dataModel :
      ∀ n, FilterRegularization.HasSemistochasticDataModel
        (K n) fTrue (d n) (η n ω0))
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : TsvdEstimation.IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_discrep :
      IsDiscrepancyChoiceFamily K d Rtsvd σ mDiscrep) :
    Asymptotics.IsEquivalent Filter.atTop
      (fun n ↦ (mDiscrep n : ℝ))
      (indexBenchmark b c p q σ) := sorry

/-- Companion `=Θ` form of `isEquivalent_indexBenchmark`. -/
theorem isTheta_indexBenchmark
    (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (K : ℕ → H →L[ℝ] F)
    (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
    (h_length : ∀ n, (S n).length = ⊤)
    (fTrue : H) (b c p q σ : ℝ)
    (η : ℕ → Ω → F) (ω0 : Ω) (d : ℕ → F)
    (Rtsvd : ℕ → ℕ → F →L[ℝ] H)
    (mDiscrep : ℕ → ℕ)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_dataModel :
      ∀ n, FilterRegularization.HasSemistochasticDataModel
        (K n) fTrue (d n) (η n ω0))
    (h_noise_memLp : ∀ n, MeasureTheory.MemLp (η n) 2 μ)
    (h_noise_meanZero : ∀ n, ∫ ω, η n ω ∂μ = 0)
    (h_noise_modeVariance :
      ∀ n i,
        ∫ ω,
          (inner ℝ ((S n).leftBasis ((S n).natIndex (h_length n) i) : F) (η n ω)) ^ 2 ∂μ =
            σ ^ 2 / (n : ℝ))
    (h_singularDecay :
      ∀ n, (S n).HasAlgebraicSingularValueSquareDecay (h_length n) c p)
    (h_fourierDecay :
      ∀ n, (S n).HasAlgebraicFourierCoefficientSquareDecay (h_length n) fTrue b q)
    (h_tsvd : TsvdEstimation.IsTsvdReconstructionFamily K S h_length Rtsvd)
    (h_discrep :
      IsDiscrepancyChoiceFamily K d Rtsvd σ mDiscrep) :
    (fun n ↦ (mDiscrep n : ℝ)) =Θ[Filter.atTop]
      indexBenchmark b c p q σ := sorry

end

end TsvdDiscrepancy

