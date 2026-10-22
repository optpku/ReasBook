/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap05.Definition_5_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators ProbabilityTheory

universe u

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Definition 15.39: A real random-variable array consists of row lengths `kₙ` together with
measurable entries `Xₙ,ᵢ`, indexed in Lean by `i : Fin (kₙ)`. -/
structure RealRandomVariableArray (Ω : Type u) [MeasurableSpace Ω] where
  rowLength : ℕ → ℕ
  entry : ∀ n, Fin (rowLength n) → Ω → ℝ
  measurable_entry : ∀ n i, Measurable (entry n i)

namespace RealRandomVariableArray

/-- A real random-variable array can be evaluated at a row index and an entry index. -/
instance : CoeFun (RealRandomVariableArray Ω) (fun A ↦ ∀ n, Fin (A.rowLength n) → Ω → ℝ) :=
  ⟨fun A ↦ A.entry⟩

/-- The row sum `Sₙ` of a real random-variable array is the sum of the entries in the `n`-th row. -/
def rowSum (A : RealRandomVariableArray Ω) (n : ℕ) : Ω → ℝ :=
  ∑ i : Fin (A.rowLength n), A n i

-- Proof sketch: unfold `rowSum` and use finite sums of measurable functions together with the
-- measurability field of the array entries.
/-- The row sum of a real random-variable array is a measurable real random variable. -/
theorem measurable_rowSum (A : RealRandomVariableArray Ω) (n : ℕ) :
    Measurable (A.rowSum n) := by
  -- First rewrite `rowSum` into the pointwise sum form used by the finite-sum measurability API.
  have hrow : A.rowSum n = fun ω ↦ ∑ i : Fin (A.rowLength n), A n i ω := by
    funext ω
    simp [RealRandomVariableArray.rowSum, Finset.sum_apply]
  rw [hrow]
  -- Each summand is measurable by the structure field, so the finite row sum is measurable.
  exact Finset.measurable_sum Finset.univ fun i _ ↦ A.measurable_entry n i

/-- The row sum of a real random-variable array is almost everywhere measurable with respect to
any ambient measure. -/
theorem aemeasurable_rowSum (A : RealRandomVariableArray Ω) (μ : Measure Ω) (n : ℕ) :
    AEMeasurable (A.rowSum n) μ :=
  (A.measurable_rowSum n).aemeasurable

/-- The law of the `n`-th row sum of a real random-variable array. -/
noncomputable abbrev rowSumLaw
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    ProbabilityMeasure ℝ :=
  ProbabilityMeasure.map ⟨μ, inferInstance⟩ (A.aemeasurable_rowSum μ n)

/-- The row-sum law is the pushforward of the underlying probability measure along the row sum. -/
theorem rowSumLaw_toMeasure
    (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] (n : ℕ) :
    (A.rowSumLaw μ n : Measure ℝ) = Measure.map (A.rowSum n) μ := by
  simp [rowSumLaw]

/-- A real random-variable array is independent if every row is an independent finite family. -/
class IsIndependent (A : RealRandomVariableArray Ω) (μ : Measure Ω) : Prop where
  rowwise : ∀ n, iIndepFun (A n) μ

/-- A real random-variable array is centered if each entry is centered in the scalar sense of
Definition 5.1. -/
class IsCentered (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop
    where
  centered : ∀ n i, _root_.IsCentered (A n i) μ

/-- In a centered array, each entry is integrable. -/
theorem IsCentered.integrable
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [hA : IsCentered A μ]
    (n : ℕ) (i : Fin (A.rowLength n)) :
    Integrable (A n i) μ :=
  (hA.centered n i).1

/-- In a centered array, each entry has expectation zero. -/
theorem IsCentered.expectation_eq_zero
    {A : RealRandomVariableArray Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] [hA : IsCentered A μ]
    (n : ℕ) (i : Fin (A.rowLength n)) :
    μ[A n i] = 0 :=
  (hA.centered n i).2

/-- A real random-variable array is normed if every entry is square-integrable and the sum of the
row variances is `1` in each row. -/
class IsNormed (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop
    where
  memLp_two : ∀ n i, MemLp (A n i) 2 μ
  variance_sum_eq_one : ∀ n, ∑ i : Fin (A.rowLength n), Var[A n i; μ] = 1

/-- A real random-variable array is a null array if it is centered and the largest tail
probability in each row tends to `0` for every fixed threshold `ε > 0`. -/
class IsNull (A : RealRandomVariableArray Ω) (μ : Measure Ω) [IsProbabilityMeasure μ] : Prop
    extends IsCentered A μ where
  asymptotically_negligible :
    ∀ ⦃ε : ℝ⦄, 0 < ε →
      Filter.Tendsto
        (fun n ↦ ⨆ i : Fin (A.rowLength n), μ {ω | ε < |A n i ω|})
        Filter.atTop (nhds 0)

end RealRandomVariableArray
