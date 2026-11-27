/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_33
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Notation_7_7
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Prop_7_20
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_11
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.Nullspace
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_12.SingularSystem
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Remark_7_17.OptimalParameter
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Theorem_7_21
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

/-!
Remark 7.22 (TSVD versus Tikhonov expected squared estimation-error optimal
parameter rates).

This source item compares the optimal expected squared estimation-error
parameter rates from `(7.65)` and `(7.80)`: when `2 * p - q > -1`, both the
TSVD and Tikhonov minimizers are proportional to
`fun n ↦ (σ^2 / n) ^ (p / (p + q))`, while when `2 * p - q < -1`, the
Tikhonov minimizer saturates at the `q`-independent rate
`fun n ↦ (σ^2 / n) ^ (p / (3 * p + 1))` and the source ties that saturated
regime to the Fourier-coefficient decay law `(7.53)`, the range condition
`f_true ∈ (K_n^* K_n).range`, and the qualitative claim that saturation does
not occur for TSVD.

This source item remains only partially formalized in the current repo
snapshot. The nonsaturated branch can already be packaged against the existing
TSVD rate theorem from `Remark 7.17`, but the saturated comparison still
lacks a source-faithful same-rate owner: the current repo exposes
`TikhonovEstimation.saturatedParameterBenchmark` with its pointwise
`‖f_true‖_{K_n^* K_n}^2` factor, while the source prose compares only the
`q`-independent rate and adds the qualitative claim that saturation does not
occur for TSVD.

Repository precedent therefore supports keeping the main labeled entry
blocker-style, while exposing only the reusable nonsaturated bridge that is
already justified by the current Chapter 7 API. The source-condition clause
for the saturated branch should still be written using `(K n).adjoint.comp
(K n)`, `LinearMap.mem_range`, and the weighted-series bridge from
`Remark 7.11` once the missing same-rate comparison surface is available.
-/

/- Remark 7.22. Main labeled check-only entry.

The full source-faithful comparison remains blocked at the saturated branch
and the “no saturation for TSVD” clause, but the current Chapter 7 development
already exposes the TSVD rate theorem from `Remark 7.17`, the Tikhonov
expected-objective and benchmark owners from `(7.80)`, the `(7.53)`
Fourier-coefficient decay owner, and the intended `K_n^* K_n` range bridge
from `Remark 7.11`. The `#check` entries below record those verified backends,
and the companion theorem after them packages the nonsaturated Tikhonov side
into the same `ParameterChoice.IsOrderOptimalWith` owner used on the TSVD
side. -/

#check ParameterChoice.IsOptimalParameterFamily

#check
  (Asymptotics.IsEquivalent Filter.atTop : (ℕ → ℝ) → (ℕ → ℝ) → Prop)

#check ParameterChoice.IsOrderOptimalWith

#check TsvdEstimation.optimalFilterParameter

#check TikhonovEstimation.expectedObjective

#check TikhonovEstimation.nonsaturatedParameterBenchmark

#check TikhonovEstimation.saturatedParameterBenchmark

#check TikhonovEstimation.adjointCompSourceNormSq

#check
  ContinuousLinearMap.SingularSystem.HasAlgebraicFourierCoefficientSquareDecay

#check
  ContinuousLinearMap.SingularSystem.adjoint_mem_range_iff_weightedSourceSeriesSummable

#check ContinuousLinearMap.adjoint_comp

#check LinearMap.mem_range

namespace TikhonovEstimation

universe u v w

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
variable {H : Type v} {F : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

variable (K : ℕ → H →L[ℝ] F)
variable (S : (n : ℕ) → ContinuousLinearMap.SingularSystem (K n))
variable (h_length : ∀ n, (S n).length = ⊤)
variable (fTrue : H) (b c p q σ : ℝ)
variable (η : ℕ → Ω → F)
variable (Rtikh : ℕ → ℝ → F →L[ℝ] H)
variable (alphaE : ℕ → ℝ)

/-- Helper for Remark 7.22: a positive constant together with the matching
asymptotic equivalence is exactly an `IsOrderOptimalWith` witness. -/
lemma orderOptimalWith_of_pos_and_isEquivalent
    {r : ℝ} {α αopt : ℕ → ℝ}
    (h : 0 < r ∧ Asymptotics.IsEquivalent Filter.atTop α (fun n ↦ r * αopt n)) :
    ParameterChoice.IsOrderOptimalWith r α αopt := by
  -- Route correction: use the owner-facing `Definition_7_33` bridge instead of
  -- reopening the wrapper definition locally.
  exact (ParameterChoice.IsOrderOptimalWith_iff r α αopt).2 h

omit [MeasureTheory.IsProbabilityMeasure μ] [CompleteSpace F] in
/-- The nonsaturated parameter formula, written as a constant times a rate. -/
lemma optimalFamily_nonsaturated_isEquivalent_scaledRate
    (h_model : PowerRisk.HasPowerRiskModel
      (expectedObjective μ K Rtikh fTrue η) (nullspaceErrorFloor K fTrue) b c p q σ)
    (h_alphaE : ParameterChoice.IsOptimalParameterFamily
      (expectedObjective μ K Rtikh fTrue η) admissibleParameters alphaE)
    (h_alphaE_pos : ∀ᶠ n in Filter.atTop, 0 < alphaE n)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_nonsaturated : -1 < 2 * p - q) :
    Asymptotics.IsEquivalent Filter.atTop alphaE
      (fun n : ℕ ↦ parameterConstantC1 b c p q * (((σ ^ 2) / (n : ℝ)) ^ (p / (p + q)))) :=
  optimalFamily_nonsaturated_isAsymptoticallyOptimal μ K fTrue b c p q σ η Rtikh alphaE
    h_model h_alphaE h_alphaE_pos h_b h_c h_p h_q h_σ h_nonsaturated

omit [MeasureTheory.IsProbabilityMeasure μ] [CompleteSpace F] in
/-- Remark 7.22: the nonsaturated Tikhonov minimizer has the same parameter
rate as TSVD, with the explicit constant from (7.80). -/
theorem optimalFamily_nonsaturated_isOrderOptimalWith
    (h_model : PowerRisk.HasPowerRiskModel
      (expectedObjective μ K Rtikh fTrue η) (nullspaceErrorFloor K fTrue) b c p q σ)
    (h_alphaE : ParameterChoice.IsOptimalParameterFamily
      (expectedObjective μ K Rtikh fTrue η) admissibleParameters alphaE)
    (h_alphaE_pos : ∀ᶠ n in Filter.atTop, 0 < alphaE n)
    (h_b : 0 < b) (h_c : 0 < c) (h_p : 1 < p) (h_q : 1 < q) (h_σ : 0 < σ)
    (h_nonsaturated : -1 < 2 * p - q) :
    ParameterChoice.IsOrderOptimalWith (parameterConstantC1 b c p q) alphaE
      (fun n ↦ ((σ ^ 2) / (n : ℝ)) ^ (p / (p + q))) := by
  exact orderOptimalWith_of_pos_and_isEquivalent
    ⟨parameterConstantC1_pos (b := b) (c := c) (p := p) (q := q)
      h_b h_c h_p h_q h_nonsaturated,
    optimalFamily_nonsaturated_isEquivalent_scaledRate μ K fTrue b c p q σ η Rtikh alphaE
      h_model h_alphaE h_alphaE_pos h_b h_c h_p h_q h_σ h_nonsaturated⟩

end

end TikhonovEstimation
