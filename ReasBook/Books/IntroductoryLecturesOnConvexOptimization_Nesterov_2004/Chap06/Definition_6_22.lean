/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_21
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap06.Definition_6_27

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators

universe u v

/-
Definition 6.22 lies in the finite max-absolute-value / log-sum-exp smoothing domain.

Sampled owner-style declarations:
- `maxTypeObjective` in `Chap02/Lemma_2_18`, the project owner for pointwise maxima of a nonempty
  finite family;
- `maxAbsoluteValueOptimizationObjective` in `Chap06/Definition_6_21`, the nearby chapter owner
  fixing the source-facing absolute-affine family `i ↦ |a i x| - b i`;
- `η` together with the positive-parameter recall surface in `Chap06/Definition_6_27`, the
  chapter's log-sum-exp owner pattern;
- `logSumExpMaxEigenvalueSmoothing` in `Chap06/Definition_6_47`, another Chapter 6 smoothing
  owner whose public surface uses a positive smoothing parameter subtype.

Best owner abstraction:
- source-facing: `logSumExpAbsoluteValueSmoothing`, since this item introduces the smoothed
  absolute-affine objective itself;
- core/canonical: the chapter/project finite-family owner pattern
  `[Fintype ι] [Nonempty ι]` together with the Chapter 6 positive-parameter smoothing surface;
- bridge/view: `logSumExpAbsoluteValueSmoothing_apply`, the direct expansion to the textbook
  formula.

Primitive data:
- a nonempty finite index family `ι`;
- linear functionals `a : ι → Module.Dual ℝ E`;
- offsets `b : ι → ℝ`, used through the same shifted absolute values `|a i x| - b i` as in
  `maxAbsoluteValueOptimizationObjective a b`;
- the positive smoothing parameter `μ : {μ : ℝ // 0 < μ}`.

Derived API:
- the source-facing smoothing function below;
- its evaluation theorem.

This file therefore stays at the source-facing layer: there is no upstream chapter owner for this
exact log-sum-exp smoothing, so the refinement is to keep the single owner declaration while
reusing the Chapter 6 absolute-affine family from `maxAbsoluteValueOptimizationObjective` instead
of introducing a parallel residual convention.
-/
variable {ι : Type v} [Fintype ι]
variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Definition 6.22: for linear functionals `a₁, …, aₘ ∈ E*`, offsets `b ∈ ℝᵐ`, and smoothing
parameter `μ > 0`, the log-sum-exp smoothing of the Chapter 6 objective
`x ↦ max_i (|a_i(x)| - bⁱ)` from Definition 6.21 is the function
`x ↦ μ log (((card ι)⁻¹) ∑ᵢ exp ((|aᵢ(x)| - bᵢ) / μ))`. The nonempty finite-family assumptions are
part of the mathematics here because the normalization factor is the average over the index
family. -/
def logSumExpAbsoluteValueSmoothing
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) : E → ℝ :=
  fun x ↦
    μ.1 * Real.log (((Fintype.card ι : ℝ)⁻¹) *
      ∑ i : ι, Real.exp ((|a i x| - b i) / μ.1))

-- Proof sketch: unfold `logSumExpAbsoluteValueSmoothing`; the displayed formula is exactly the
-- normalized log-sum-exp smoothing of the same family `i ↦ |a i x| - b i` used in
-- `maxAbsoluteValueOptimizationObjective`.
/-- Evaluating `logSumExpAbsoluteValueSmoothing a b μ` gives the defining averaged logarithmic
smoothing formula built from the shifted absolute values `|aᵢ(x)| - bᵢ`. -/
@[simp] theorem logSumExpAbsoluteValueSmoothing_apply
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    logSumExpAbsoluteValueSmoothing a b μ x =
      μ.1 * Real.log (((Fintype.card ι : ℝ)⁻¹) *
        ∑ i : ι, Real.exp ((|a i x| - b i) / μ.1)) :=
  rfl

-- Proof sketch: apply `eta_apply` to the score vector
-- `i ↦ |a i x| - b i`, then separate the normalization factor `(card ι : ℝ)⁻¹`
-- from the logarithm using the standard `Real.log_mul` identity.
/-- Definition 6.22 is the Chapter 6 log-sum-exp potential `η` applied to the shifted
absolute-value score vector, together with the additive normalization term coming from averaging
over the finite index family. -/
theorem logSumExpAbsoluteValueSmoothing_eq_eta_add_log_card_inv
    [Nonempty ι] (a : ι → Module.Dual ℝ E) (b : ι → ℝ) (μ : {μ : ℝ // 0 < μ}) (x : E) :
    logSumExpAbsoluteValueSmoothing a b μ x =
      η μ (WithLp.toLp 2 fun i : ι ↦ |a i x| - b i) +
        μ.1 * Real.log ((Fintype.card ι : ℝ)⁻¹) := by
  let u : EuclideanSpace ℝ ι := WithLp.toLp 2 fun i : ι ↦ |a i x| - b i
  have hcard_inv_ne : ((Fintype.card ι : ℝ)⁻¹) ≠ 0 := by
    -- The averaging factor is nonzero because a nonempty finite type has nonzero cardinality.
    exact inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hsum_pos : 0 < ∑ i : ι, Real.exp ((|a i x| - b i) / μ.1) := by
    obtain ⟨i0⟩ := ‹Nonempty ι›
    -- A single strictly positive exponential term forces the whole finite sum to be positive.
    refine Finset.sum_pos' ?_ ?_
    · intro i hi
      exact Real.exp_nonneg ((|a i x| - b i) / μ.1)
    · exact ⟨i0, Finset.mem_univ i0, Real.exp_pos ((|a i0 x| - b i0) / μ.1)⟩
  have heta :
      η μ u = μ.1 * Real.log (∑ i : ι, Real.exp ((|a i x| - b i) / μ.1)) := by
    -- Rewriting `η` on the score vector isolates the same exponential sum as in the smoothing.
    simpa [u] using eta_apply μ u
  -- Split the logarithm of the average into the normalization term and the `η` term.
  calc
    logSumExpAbsoluteValueSmoothing a b μ x
        = μ.1 *
            (Real.log ((Fintype.card ι : ℝ)⁻¹) +
              Real.log (∑ i : ι, Real.exp ((|a i x| - b i) / μ.1))) := by
            rw [logSumExpAbsoluteValueSmoothing_apply, Real.log_mul hcard_inv_ne hsum_pos.ne']
    _ = μ.1 * Real.log ((Fintype.card ι : ℝ)⁻¹) +
          μ.1 * Real.log (∑ i : ι, Real.exp ((|a i x| - b i) / μ.1)) := by
          ring
    _ = μ.1 * Real.log ((Fintype.card ι : ℝ)⁻¹) + η μ u := by
          rw [heta]
    _ = η μ (WithLp.toLp 2 fun i : ι ↦ |a i x| - b i) +
          μ.1 * Real.log ((Fintype.card ι : ℝ)⁻¹) := by
          simp [u, add_comm]

end
