/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Extr

-- Declarations for this item will be appended below by the statement pipeline.

-- Semantic recall: `lean_leansearch` surfaced `IsMinOn` as the canonical owner for
-- “`φ (αStar) = min_{α ≥ 0} φ α`”, and nearby Chapter 2 files use `Set.Ici 0` for
-- nonnegative exact line-search domains.

open Set

/-- Chapter02 Definition 2.1.1. For the one-dimensional minimization problem
`min_{α ≥ 0} φ α`, a closed interval `Icc a b` is a search interval when
`αStar` is a minimizer of `φ` on `Ici 0`, `αStar ∈ Icc a b`, and
`Icc a b ⊆ Ici 0`. The same interval is also called an interval of
uncertainty. -/
def IsSearchInterval (φ : ℝ → ℝ) (αStar a b : ℝ) : Prop :=
  IsMinOn φ (Ici 0) αStar ∧
    αStar ∈ Icc a b ∧
    Icc a b ⊆ Ici (0 : ℝ)

/-- Unfolding specification for `IsSearchInterval`. -/
theorem isSearchInterval_iff {φ : ℝ → ℝ} {αStar a b : ℝ} :
    IsSearchInterval φ αStar a b ↔
      IsMinOn φ (Ici 0) αStar ∧
        αStar ∈ Icc a b ∧
        Icc a b ⊆ Ici (0 : ℝ) :=
  Iff.rfl

/-- A search interval keeps the source minimizer condition on the nonnegative ray. -/
theorem IsSearchInterval.isMinOn {φ : ℝ → ℝ} {αStar a b : ℝ}
    (h_search : IsSearchInterval φ αStar a b) :
    IsMinOn φ (Ici 0) αStar :=
  h_search.1

/-- A search interval includes the designated minimizer in its underlying closed interval. -/
theorem IsSearchInterval.mem_Icc {φ : ℝ → ℝ} {αStar a b : ℝ}
    (h_search : IsSearchInterval φ αStar a b) :
    αStar ∈ Icc a b :=
  h_search.2.1

/-- A search interval lies in the nonnegative ray. -/
theorem IsSearchInterval.subset_nonneg {φ : ℝ → ℝ} {αStar a b : ℝ}
    (h_search : IsSearchInterval φ αStar a b) :
    Icc a b ⊆ Ici (0 : ℝ) :=
  h_search.2.2
