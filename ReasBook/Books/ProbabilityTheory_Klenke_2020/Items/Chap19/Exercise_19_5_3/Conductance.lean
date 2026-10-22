/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap19.Definition_19_23

open scoped BigOperators ENNReal

noncomputable section

universe u

namespace ProbabilityTheory

/-- Local owner repair for Exercise 19.5.3: the Dirichlet energy series attached to a conductance
network. -/
def dirichletEnergySeries {E : Type u} (C : E → E → ℝ≥0∞) (u : E → ℝ) : ℝ :=
  (1 / 2 : ℝ) *
    ∑' e : E × E, (C e.1 e.2).toReal * (u e.1 - u e.2) ^ (2 : ℕ)

/-- Local owner repair for Exercise 19.5.3: a potential has finite Dirichlet energy when the edge
energy series is summable over all ordered edges. -/
def HasFiniteDirichletEnergy {E : Type u} (C : E → E → ℝ≥0∞) (u : E → ℝ) : Prop :=
  Summable (fun e : E × E ↦ (C e.1 e.2).toReal * (u e.1 - u e.2) ^ (2 : ℕ))

/-- Local owner repair for Exercise 19.5.3: unfold `HasFiniteDirichletEnergy` as summability of
the ordered-edge energy series. -/
theorem hasFiniteDirichletEnergy_iff {E : Type u} (C : E → E → ℝ≥0∞) (u : E → ℝ) :
    HasFiniteDirichletEnergy C u ↔
      Summable (fun e : E × E ↦ (C e.1 e.2).toReal * (u e.1 - u e.2) ^ (2 : ℕ)) := by
  rfl

/-- Local owner repair for Exercise 19.5.3: the effective conductance between two boundary sets,
defined by the Dirichlet principle over finite-energy unit-boundary potentials. This keeps the
source-facing statement stable while excluding nonsummable potentials on the bi-infinite ladder. -/
def dirichletEffectiveConductance {E : Type u}
    (C : E → E → ℝ≥0∞) (A0 A1 : Set E) : ℝ :=
  sInf <|
    dirichletEnergySeries C ''
      {u : E → ℝ |
        HasFiniteDirichletEnergy C u ∧
          Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}

/-- Local owner repair for Exercise 19.5.3: unfolding `dirichletEffectiveConductance` reduces the
statement to the Dirichlet-energy infimum over finite-energy unit-boundary potentials. -/
theorem dirichletEffectiveConductance_def {E : Type u}
    (C : E → E → ℝ≥0∞) (A0 A1 : Set E) :
    dirichletEffectiveConductance C A0 A1 =
      (sInf <|
        dirichletEnergySeries C ''
          {u : E → ℝ |
            HasFiniteDirichletEnergy C u ∧
              Set.EqOn u (fun _ : E ↦ 0) A0 ∧ Set.EqOn u (fun _ : E ↦ 1) A1}) := rfl

end ProbabilityTheory
