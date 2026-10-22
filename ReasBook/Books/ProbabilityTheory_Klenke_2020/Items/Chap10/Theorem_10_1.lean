/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory

universe u

variable {Ω : Type u} [mΩ : MeasurableSpace Ω]
variable {μ : Measure Ω}
variable {ℱ : Filtration ℕ mΩ}

-- Proof sketch: use `Adapted.stronglyAdapted` to upgrade the real-valued adapted process to a
-- strongly adapted one, apply `martingale_martingalePart` to the canonical martingale part, use
-- `isPredictable_of_measurable_add_one` together with `predictablePart_zero` and
-- `stronglyAdapted_predictablePart`, and conclude from
-- `martingalePart_add_predictablePart`.
/-- Theorem 10.1 (1): the canonical pair consisting of `martingalePart X ℱ μ` and
`predictablePart X ℱ μ` is a Doob decomposition of an adapted integrable real-valued process `X`.
-/
theorem canonical_doobDecomposition [SigmaFiniteFiltration μ ℱ] {X : ℕ → Ω → ℝ}
    (hX_adapted : Adapted ℱ X)
    (hX_int : ∀ n, Integrable (X n) μ) :
    IsPredictable ℱ (predictablePart X ℱ μ) ∧
      predictablePart X ℱ μ 0 = 0 ∧
      Martingale (martingalePart X ℱ μ) ℱ μ ∧
      martingalePart X ℱ μ + predictablePart X ℱ μ = X := by
  have hPredictablePart : StronglyAdapted ℱ (fun n ↦ predictablePart X ℱ μ (n + 1)) :=
    stronglyAdapted_predictablePart
  refine ⟨?_, predictablePart_zero, martingale_martingalePart hX_adapted.stronglyAdapted hX_int,
    martingalePart_add_predictablePart ℱ μ X⟩
  refine isPredictable_of_measurable_add_one ?_ fun n ↦
    (hPredictablePart n).measurable
  simpa [predictablePart_zero] using
    (stronglyMeasurable_zero : StronglyMeasurable[ℱ 0] (0 : Ω → ℝ)).measurable

section DoobDecomposition

variable {X M A : ℕ → Ω → ℝ}

private theorem stronglyAdapted_succ_of_predictable (hA_pred : IsPredictable ℱ A) :
    StronglyAdapted ℱ fun n ↦ A (n + 1) := by
  have hA_adapted : Adapted ℱ fun n ↦ A (n + 1) :=
    fun n ↦ hA_pred.measurable_add_one n
  exact hA_adapted.stronglyAdapted

private theorem integrable_predictable_component (hM : Martingale M ℱ μ) (hMX : M + A = X)
    (hX_int : ∀ n, Integrable (X n) μ) :
    ∀ n, Integrable (A n) μ := by
  intro n
  have hA_eq : A n = X n - M n := by
    ext ω
    exact eq_sub_iff_add_eq.mpr (by simpa [add_comm] using congrFun (congrFun hMX n) ω)
  simpa [hA_eq] using (hX_int n).sub (hM.integrable n)

-- Proof sketch: rewrite `X` using `hMX`, convert `hA_pred` into the strong adaptation hypothesis
-- required by `predictablePart_add_ae_eq`, derive integrability of `A n` from `hMX`, and apply
-- the uniqueness of the predictable part.
/-- Theorem 10.1 (2): in any Doob decomposition `X = M + A`, the predictable component `A` agrees
almost everywhere at each time with the canonical predictable part `predictablePart X ℱ μ`. -/
theorem doobDecomposition_predictablePart_ae_eq [SigmaFiniteFiltration μ ℱ] (hM : Martingale M ℱ μ)
    (hA_pred : IsPredictable ℱ A) (hA_zero : A 0 = 0) (hMX : M + A = X)
    (hX_int : ∀ n, Integrable (X n) μ) :
    ∀ n, A n =ᵐ[μ] predictablePart X ℱ μ n := by
  have hA : StronglyAdapted ℱ fun n ↦ A (n + 1) :=
    stronglyAdapted_succ_of_predictable hA_pred
  have hA_int : ∀ n, Integrable (A n) μ :=
    integrable_predictable_component hM hMX hX_int
  intro n
  simpa [hMX] using
    (predictablePart_add_ae_eq hM hA hA_zero hA_int n).symm

-- Proof sketch: rewrite `X` using `hMX`, apply `martingalePart_add_ae_eq` to the decomposition
-- `M + A`, and combine it with the predictable-part uniqueness statement above.
/-- Theorem 10.1 (3): in any Doob decomposition `X = M + A`, the martingale component `M` agrees
almost everywhere at each time with the canonical martingale part `martingalePart X ℱ μ`. -/
theorem doobDecomposition_martingalePart_ae_eq [SigmaFiniteFiltration μ ℱ] (hM : Martingale M ℱ μ)
    (hA_pred : IsPredictable ℱ A) (hA_zero : A 0 = 0) (hMX : M + A = X)
    (hX_int : ∀ n, Integrable (X n) μ) :
    ∀ n, M n =ᵐ[μ] martingalePart X ℱ μ n := by
  have hA : StronglyAdapted ℱ fun n ↦ A (n + 1) :=
    stronglyAdapted_succ_of_predictable hA_pred
  have hA_int : ∀ n, Integrable (A n) μ :=
    integrable_predictable_component hM hMX hX_int
  intro n
  simpa [hMX] using
    (martingalePart_add_ae_eq hM hA hA_zero hA_int n).symm

end DoobDecomposition

-- Proof sketch: use `submartingale_iff_condExp_sub_nonneg` to characterize submartingales by
-- nonnegativity of the one-step conditional expected increments, identify those increments with
-- the successive differences of `predictablePart X ℱ μ`, and convert the nonnegative differences
-- into almost-sure pathwise monotonicity.
/-- A submartingale has an almost surely monotone canonical predictable part. This isolates the
forward owner-facing direction of Theorem 10.1 (4) so it can be reused without the extra
finite-measure hypothesis needed only for the converse implication. -/
theorem submartingale_ae_monotone_predictablePart {X : ℕ → Ω → ℝ}
    (hX_sub : Submartingale X ℱ μ) :
    ∀ᵐ ω ∂μ, Monotone (fun n ↦ predictablePart X ℱ μ n ω) := by
  refine (ae_all_iff.2 fun n ↦ ?_).mono fun ω hω ↦ monotone_nat_of_le_succ hω
  have hstep : 0 ≤ᵐ[μ] μ[X (n + 1) - X n | ℱ n] :=
    hX_sub.condExp_sub_nonneg n.le_succ
  simpa [predictablePart, Finset.sum_range_succ] using hstep

/-- Theorem 10.1 (4): an adapted integrable real-valued process is a submartingale if and only if
its canonical predictable part is almost surely monotone increasing in time. -/
theorem submartingale_iff_ae_monotone_predictablePart [IsFiniteMeasure μ] {X : ℕ → Ω → ℝ}
    (hX_adapted : Adapted ℱ X) (hX_int : ∀ n, Integrable (X n) μ) :
    Submartingale X ℱ μ ↔ ∀ᵐ ω ∂μ, Monotone (fun n ↦ predictablePart X ℱ μ n ω) := by
  constructor
  · exact submartingale_ae_monotone_predictablePart
  · intro hmono
    refine submartingale_of_condExp_sub_nonneg_nat hX_adapted.stronglyAdapted hX_int fun n ↦ ?_
    have hstep : predictablePart X ℱ μ n ≤ᵐ[μ] predictablePart X ℱ μ (n + 1) := by
      filter_upwards [hmono] with ω hω
      exact hω n.le_succ
    filter_upwards [hstep] with ω hω
    simpa [predictablePart, Finset.sum_range_succ] using hω
