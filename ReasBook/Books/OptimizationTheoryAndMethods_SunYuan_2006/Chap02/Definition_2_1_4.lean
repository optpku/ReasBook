/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap02.Definition_2_1_3

-- Semantic recall: `lean_leansearch` surfaced `StrictAntiOn` and
-- `StrictMonoOn` as the canonical mathlib interval-monotonicity predicates.
-- Following the owner introduced in `Chapter02 Definition 2.1.3`, this
-- item bridges the turning-point order condition to `unimodalOn`.

/-- A candidate turning point whose values strictly decrease up to it and
strictly increase from it on `Set.Icc a b`. -/
structure TurningPointOrderCondition (φ : ℝ → ℝ) (a b : ℝ) (αStar : Set.Icc a b) : Prop where
  left_of_lt :
    ∀ ⦃α₁ α₂ : ℝ⦄,
      α₁ ∈ Set.Icc a b →
      α₂ ∈ Set.Icc a b →
      α₁ < α₂ →
      α₂ ≤ αStar →
      φ α₁ > φ α₂
  right_of_lt :
    ∀ ⦃α₁ α₂ : ℝ⦄,
      α₁ ∈ Set.Icc a b →
      α₂ ∈ Set.Icc a b →
      α₁ < α₂ →
      αStar ≤ α₁ →
      φ α₁ < φ α₂

namespace TurningPointOrderCondition

theorem strictAntiOn {φ : ℝ → ℝ} {a b : ℝ} {αStar : Set.Icc a b}
    (h : TurningPointOrderCondition φ a b αStar) :
    StrictAntiOn φ (Set.Icc a αStar) := by
  intro α₁ hα₁ α₂ hα₂ hlt
  exact h.left_of_lt
    ⟨hα₁.1, le_trans hα₁.2 αStar.2.2⟩
    ⟨hα₂.1, le_trans hα₂.2 αStar.2.2⟩
    hlt
    hα₂.2

theorem strictMonoOn {φ : ℝ → ℝ} {a b : ℝ} {αStar : Set.Icc a b}
    (h : TurningPointOrderCondition φ a b αStar) :
    StrictMonoOn φ (Set.Icc αStar b) := by
  intro α₁ hα₁ α₂ hα₂ hlt
  exact h.right_of_lt
    ⟨le_trans αStar.2.1 hα₁.1, hα₁.2⟩
    ⟨le_trans αStar.2.1 hα₂.1, hα₂.2⟩
    hlt
    hα₁.1

end TurningPointOrderCondition

/-- Chapter02 Definition 2.1.4. If there exists
`αStar : Set.Icc a b` satisfying `TurningPointOrderCondition φ a b αStar`,
then `φ` is unimodal on `Set.Icc a b`. -/
theorem unimodalOn_of_existsTurningPointOrderCondition
    {φ : ℝ → ℝ} {a b : ℝ}
    (h : ∃ αStar : Set.Icc a b, TurningPointOrderCondition φ a b αStar) :
    unimodalOn φ a b := by
  rw [unimodalOn_iff]
  rcases h with ⟨αStar, hαStar⟩
  exact ⟨αStar, αStar.2, hαStar.strictAntiOn, hαStar.strictMonoOn⟩

/-- A stronger unique-existence hypothesis still implies unimodality through
`unimodalOn_of_existsTurningPointOrderCondition`. If there exists a unique
`αStar : Set.Icc a b` satisfying `TurningPointOrderCondition φ a b αStar`,
then `φ` is unimodal on `Set.Icc a b`. -/
theorem unimodalOn_of_existsUniqueTurningPointOrderCondition
    {φ : ℝ → ℝ} {a b : ℝ}
    (h : ∃! αStar : Set.Icc a b, TurningPointOrderCondition φ a b αStar) :
    unimodalOn φ a b := by
  exact unimodalOn_of_existsTurningPointOrderCondition h.exists
