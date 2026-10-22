/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap26.Definition_26_20

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {n : ℕ}

local notation "State" => Fin n → ℝ
local notation "PathSpace" => EuclideanPathSpace n
local notation "DiffusionMatrixCoeff" => NNReal → State → Fin n → Fin n → ℝ
local notation "DriftCoeff" => NNReal → State → Fin n → ℝ

/-- Definition 26.23: the local martingale problem `LMP(a, b)` is well-posed if, for every
starting point `x ∈ ℝⁿ`, there exists a realization of `LMP(a, b, Measure.dirac x)` and that
Dirac-initial martingale problem is unique in law. -/
def LocalMartingaleProblemWellPosed
    (a : DiffusionMatrixCoeff) (b : DriftCoeff) : Prop :=
  ∀ x : State,
    (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
        (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
        IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X) ∧
      LocalMartingaleProblemHasUniqueLaw.{u, v} (Measure.dirac x) a b

-- Proof sketch: unfold `LocalMartingaleProblemWellPosed`; it requires, for each start point `x`,
-- existence of a realization of `LMP(a, b, Measure.dirac x)` together with uniqueness in law for
-- all solutions started from the same Dirac mass.
/-- Unfolding `LocalMartingaleProblemWellPosed a b` gives existence and uniqueness in law for every
Dirac initial distribution `δₓ`. -/
theorem localMartingaleProblemWellPosed_iff
    {a : DiffusionMatrixCoeff} {b : DriftCoeff} :
    LocalMartingaleProblemWellPosed.{u, v} a b ↔
      ∀ x : State,
        (∃ (Ω : Type u) (mΩ : MeasurableSpace Ω) (ℱ : Filtration NNReal mΩ)
            (P : ProbabilityMeasure Ω) (X : Ω → PathSpace),
            IsLocalMartingaleProblemSolution (Measure.dirac x) a b ℱ (P : Measure Ω) X) ∧
          LocalMartingaleProblemHasUniqueLaw.{u, v} (Measure.dirac x) a b := by
  rfl

end ProbabilityTheory
