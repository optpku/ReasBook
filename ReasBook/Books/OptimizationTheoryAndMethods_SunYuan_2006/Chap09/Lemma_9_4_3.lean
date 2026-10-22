/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import OptimizationTheoryAndMethods_SunYuan_2006.Chap09.Algorithm_9_4_2

noncomputable section

section Chapter09Lemma943

variable {n me mi : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

namespace QuadraticProgram

/-- The source eventual-constancy condition `(9.4.30)` for an active-set method: once the stage
`k₀` is reached, every later iterate equals the common iterate `x k₀ = x̄`. -/
def ActiveSetMethod.satisfies9430
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k₀ : ℕ) : Prop :=
  ∀ ⦃k : ℕ⦄, k₀ ≤ k → A.x k = A.x k₀

/-- Unfolding `ActiveSetMethod.satisfies9430` gives the eventual-constant iterate condition
used for `(9.4.30)`. -/
theorem ActiveSetMethod.satisfies9430_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k₀ : ℕ) :
    A.satisfies9430 k₀ ↔ ∀ ⦃k : ℕ⦄, k₀ ≤ k → A.x k = A.x k₀ := sorry

/-- The source condition `(9.4.35)` at stage `k`: the Step-2 zero-direction branch occurs and
removes the leaving inequality from the working set. -/
def ActiveSetMethod.satisfies9435
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) : Prop :=
  A.direction k = 0 ∧
    ZeroDirectionDropState
      (A.workingSet k)
      (A.workingSet (k + 1))
      (A.x k)
      (A.x (k + 1))
      (A.ineqMultiplier k)
      (A.leavingIndex k)

/-- Unfolding `ActiveSetMethod.satisfies9435` gives the zero-direction Step-2 drop condition
used for `(9.4.35)`. -/
theorem ActiveSetMethod.satisfies9435_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) :
    A.satisfies9435 k ↔
      A.direction k = 0 ∧
        ZeroDirectionDropState
          (A.workingSet k)
          (A.workingSet (k + 1))
          (A.x k)
          (A.x (k + 1))
          (A.ineqMultiplier k)
          (A.leavingIndex k) := sorry

/-- If stage `k` satisfies `(9.4.35)`, then the next inequality working set is obtained by
erasing the leaving index selected at stage `k`. -/
theorem ActiveSetMethod.workingSet_succ_eq_erase_of_satisfies9435
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k : ℕ}
    (h9435 : A.satisfies9435 k) :
    A.workingSet (k + 1) = (A.workingSet k).erase (A.leavingIndex k) := sorry

/-- The source condition `(9.4.36)` at stage `k + 1`: the successor stage has a nonzero
search direction. In this active-set owner, the Step-3 rule `(9.4.24)` already forces every
nonzero-direction step to have positive step size, so `(9.4.36)` is recorded directly on the
successor direction. -/
def ActiveSetMethod.satisfies9436
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) : Prop :=
  A.direction (k + 1) ≠ 0

/-- Unfolding `ActiveSetMethod.satisfies9436` gives the successor-stage nonzero-direction
condition used for `(9.4.36)`. -/
theorem ActiveSetMethod.satisfies9436_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) :
    A.satisfies9436 k ↔ A.direction (k + 1) ≠ 0 := sorry

/-- The source working set `𝒮_k` is the fixed equality index set `E`, represented by
`Fin me`, together with the stored inequality working set `A.workingSet k`. -/
def ActiveSetMethod.sourceWorkingSet
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) : Finset (Sum (Fin me) (Fin mi)) :=
  Finset.univ.image Sum.inl ∪ (A.workingSet k).image Sum.inr

/-- Unfolding `ActiveSetMethod.sourceWorkingSet` makes the source representation
`𝒮_k = E ∪` the stored inequality working set explicit. -/
theorem ActiveSetMethod.sourceWorkingSet_def
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k : ℕ) :
    A.sourceWorkingSet k = Finset.univ.image Sum.inl ∪ (A.workingSet k).image Sum.inr := sorry

/-- The source working sets differ exactly when their inequality parts differ, because the
equality part `E` is fixed across all stages. -/
theorem ActiveSetMethod.sourceWorkingSet_ne_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k₁ k₂ : ℕ} :
    A.sourceWorkingSet k₂ ≠ A.sourceWorkingSet k₁ ↔ A.workingSet k₂ ≠ A.workingSet k₁ := sorry

/-- The source condition `(9.4.37)` is the persistence inclusion `𝒮_{k + 2} ⊆ 𝒮_{k₂}`. -/
def ActiveSetMethod.satisfies9437
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k k₂ : ℕ) : Prop :=
  A.sourceWorkingSet (k + 2) ⊆ A.sourceWorkingSet k₂

/-- Unfolding `ActiveSetMethod.satisfies9437` gives the persistence inclusion used for
`(9.4.37)`. -/
theorem ActiveSetMethod.satisfies9437_iff
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) (k k₂ : ℕ) :
    A.satisfies9437 k k₂ ↔ A.sourceWorkingSet (k + 2) ⊆ A.sourceWorkingSet k₂ := sorry

/-- Chapter09 Lemma 9.4.3: let `k₀` satisfy `(9.4.30)`. If `k₂ > k₁ > k₀` satisfy the source
conditions `(9.4.35)`-`(9.4.37)`, then `𝒮_{k₂} ≠ 𝒮_{k₁}`. This is the source conclusion
`(9.4.38)`. -/
theorem ActiveSetMethod.sourceWorkingSet_ne_of_eventuallyConstant_of_drop_then_nonzeroDirection
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k₀ k₁ k₂ : ℕ}
    (hk₀₁ : k₀ < k₁) (hk₁₂ : k₁ < k₂)
    (h9430 : A.satisfies9430 k₀)
    (h9435 : A.satisfies9435 k₁)
    (h9436 : A.satisfies9436 k₁)
    (h9437 : A.satisfies9437 k₁ k₂) :
    A.sourceWorkingSet k₂ ≠ A.sourceWorkingSet k₁ := sorry

/-- The source conclusion `𝒮_{k₂} ≠ 𝒮_{k₁}` from Lemma 9.4.3 implies the inequality-part
working sets stored by the algorithm also differ. -/
theorem
    ActiveSetMethod.workingSet_ne_of_satisfies9430_of_zeroDirectionDrop_of_successorNonzeroDirection
    {P : QuadraticProgram n me mi} {x1 : Point}
    (A : ActiveSetMethod P x1) {k₀ k₁ k₂ : ℕ}
    (hk₀₁ : k₀ < k₁) (hk₁₂ : k₁ < k₂)
    (h9430 : A.satisfies9430 k₀)
    (h9435 : A.satisfies9435 k₁)
    (h9436 : A.satisfies9436 k₁)
    (h9437 : A.satisfies9437 k₁ k₂) :
    A.workingSet k₂ ≠ A.workingSet k₁ := sorry

end QuadraticProgram

end Chapter09Lemma943
