/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_32

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

namespace MeasureTheory.ProbabilityMeasure

-- Proof sketch: affine maps on `ℝ` are continuous, hence measurable.
/-- Affine self-maps of `ℝ` are measurable. -/
theorem measurable_affineMap (a d : ℝ) : Measurable (fun x : ℝ ↦ a * x + d) := by
  simpa using (measurable_const.mul measurable_id).add measurable_const

/-- Definition 16.20: a probability law on `ℝ` is stable in the broad sense if it is not a Dirac
mass and every positive convolution power is an affine image of the original law. -/
def IsStableInBroadSense (μ : ProbabilityMeasure ℝ) : Prop :=
  (∀ x : ℝ, μ ≠ diracProba x) ∧
    ∃ a : ℕ+ → ℝ, ∃ d : ℕ+ → ℝ,
      (∀ n : ℕ+, 0 ≤ a n) ∧
        ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable

-- Proof sketch: unpack the second component of `IsStableInBroadSense`.
/-- A broadly stable law admits nonnegative scale factors and shifts realizing every positive
convolution power as an affine image of the original law. -/
theorem IsStableInBroadSense.exists_scale_shift
    {μ : ProbabilityMeasure ℝ} (hμ : IsStableInBroadSense μ) :
    ∃ a : ℕ+ → ℝ, ∃ d : ℕ+ → ℝ,
      (∀ n : ℕ+, 0 ≤ a n) ∧
        ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) (d n)).aemeasurable :=
  hμ.2

/-- A probability law on `ℝ` is stable in the strict sense if it is not a Dirac mass and every
positive convolution power is a scaled image of the original law, with no translation term. -/
def IsStable (μ : ProbabilityMeasure ℝ) : Prop :=
  (∀ x : ℝ, μ ≠ diracProba x) ∧
    ∃ a : ℕ+ → ℝ,
      (∀ n : ℕ+, 0 ≤ a n) ∧
        ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) 0).aemeasurable

-- Proof sketch: unpack the second component of `IsStable`.
/-- A strictly stable law admits nonnegative scale factors whose positive convolution powers are
obtained without any translation term. -/
theorem IsStable.exists_scale
    {μ : ProbabilityMeasure ℝ} (hμ : IsStable μ) :
    ∃ a : ℕ+ → ℝ,
      (∀ n : ℕ+, 0 ≤ a n) ∧
        ∀ n : ℕ+, μ ^ (n : ℕ) = map μ (measurable_affineMap (a n) 0).aemeasurable :=
  hμ.2

/-- A probability law on `ℝ` is stable in the broad sense with index `α ∈ (0,2]` if it is not a
Dirac mass and its positive convolution powers are obtained with the canonical scale
`n ^ (1 / α)` up to translation. -/
def IsStableInBroadSenseWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  (∀ x : ℝ, μ ≠ diracProba x) ∧
    α ∈ Set.Ioc (0 : ℝ) 2 ∧
      ∃ d : ℕ+ → ℝ,
        ∀ n : ℕ+,
          μ ^ (n : ℕ) =
            map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable

/-- A broadly stable law with index `α` admits a centering sequence whose affine rescalings realize
all positive convolution powers. -/
theorem IsStableInBroadSenseWithIndex.exists_centering
    {μ : ProbabilityMeasure ℝ} {α : ℝ} (hμ : IsStableInBroadSenseWithIndex μ α) :
    ∃ d : ℕ+ → ℝ,
      ∀ n : ℕ+,
        μ ^ (n : ℕ) =
          map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) (d n)).aemeasurable :=
  hμ.2.2

-- Proof sketch: unpack the index-range witness carried by
-- `IsStableInBroadSenseWithIndex`.
/-- The index of a broadly stable law with index belongs to `(0,2]`. -/
theorem IsStableInBroadSenseWithIndex.index_mem_Ioc
    {μ : ProbabilityMeasure ℝ} {α : ℝ} (hμ : IsStableInBroadSenseWithIndex μ α) :
    α ∈ Set.Ioc (0 : ℝ) 2 :=
  hμ.2.1

/-- A probability law on `ℝ` is stable with index `α ∈ (0,2]` if it is not a Dirac mass and its
positive convolution powers are obtained with the canonical scale `n ^ (1 / α)` and zero
translation. -/
def IsStableWithIndex (μ : ProbabilityMeasure ℝ) (α : ℝ) : Prop :=
  (∀ x : ℝ, μ ≠ diracProba x) ∧
    α ∈ Set.Ioc (0 : ℝ) 2 ∧
      ∀ n : ℕ+,
        μ ^ (n : ℕ) =
          map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable

/-- A strictly stable law with index `α` satisfies the canonical scaling relation for every
positive convolution power. -/
theorem IsStableWithIndex.scaling
    {μ : ProbabilityMeasure ℝ} {α : ℝ} (hμ : IsStableWithIndex μ α) :
    ∀ n : ℕ+,
      μ ^ (n : ℕ) =
        map μ (measurable_affineMap ((n : ℝ) ^ (1 / α)) 0).aemeasurable :=
  hμ.2.2

-- Proof sketch: unpack the index-range witness carried by `IsStableWithIndex`.
/-- The index of a strictly stable law belongs to `(0,2]`. -/
theorem IsStableWithIndex.index_mem_Ioc
    {μ : ProbabilityMeasure ℝ} {α : ℝ} (hμ : IsStableWithIndex μ α) :
    α ∈ Set.Ioc (0 : ℝ) 2 :=
  hμ.2.1

end MeasureTheory.ProbabilityMeasure
