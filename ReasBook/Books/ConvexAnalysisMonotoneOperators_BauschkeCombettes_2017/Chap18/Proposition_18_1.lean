/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap16.Proposition_16_17

-- Declarations for this item will be appended below by the statement pipeline.

universe u

namespace ERealFunction

section ContinuitySet

variable {H : Type u} [NormedAddCommGroup H]

/- Source/core/bridge triage:
- `source-facing`: the textbook continuity set `cont f` records the ambient continuity points of
  the finite-valued representative together with the local effective-domain witness needed to avoid
  collapsing exterior `⊤` values through `EReal.toReal`.
- `core/canonical`: the primitive data are a positive ball contained in `effectiveDomain f` and
  ambient continuity of `fun y ↦ (f y : EReal).toReal`.
- `bridge/view`: Chapter 16's `ContinuousAtOnEffectiveDomain f x` is the restriction-level view
  obtained from a point of `cont f`.
-/

/-- The textbook continuity set `cont f`: points admitting a neighborhood contained in
`effectiveDomain f` on which the finite-valued representative of `f` is ambiently continuous. -/
def cont (f : H → Set.Ioi (⊥ : EReal)) : Set H :=
  {x | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
    ContinuousAt (fun y ↦ (f y : EReal).toReal) x}

/-- Membership in `cont f` is exactly the source-facing local effective-domain continuity datum. -/
@[simp] theorem mem_cont_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) :
    x ∈ cont f ↔
      ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
        ContinuousAt (fun y ↦ (f y : EReal).toReal) x :=
  Iff.rfl

/-- A point of `cont f` lies in the effective domain of `f`. -/
theorem mem_effectiveDomain_of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    x ∈ effectiveDomain f := by
  rcases hx with ⟨ρ, hρ, hball, _⟩
  exact hball (Metric.mem_ball_self hρ)

/-- A point of `cont f` is an interior point of the effective domain. -/
theorem mem_interior_effectiveDomain_of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    x ∈ interior (effectiveDomain f) := by
  rcases hx with ⟨ρ, hρ, hball, _⟩
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds x hρ) hball

/-- The Chapter 16 continuity-on-the-effective-domain owner is the restricted view of a point of
`cont f`. -/
theorem ContinuousAtOnEffectiveDomain.of_mem_cont
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∈ cont f) :
    ContinuousAtOnEffectiveDomain f x := by
  rcases hx with ⟨ρ, hρ, hball, hcont⟩
  exact ⟨hball (Metric.mem_ball_self hρ), hcont.continuousWithinAt⟩

end ContinuitySet

section SymmetricSecondDifferences

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]

/- Source/core/bridge triage:
- `source-facing`: Proposition 18.1 characterizes Fréchet differentiability by small symmetric
  second differences on the unit sphere.
- `core/canonical`: the primitive Chapter 18 owner is the unit-sphere symmetric second-difference
  quotient set and its `ε`-sublevel predicate at a point.
- `bridge/view`: Proposition 18.2 packages that pointwise predicate into the open set `S_ε`.
-/

/-- The unit-sphere symmetric second-difference quotients of `f` at `x` with step size `η`. -/
noncomputable def symmetricSecondDifferenceQuotientSet
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (η : Set.Ioi (0 : ℝ)) : Set EReal :=
  (fun y : H ↦
      ((f (x + (η : ℝ) • y) : EReal) +
          (f (x - (η : ℝ) • y) : EReal) -
          2 * (f x : EReal)) /
        (η : ℝ)) '' Metric.sphere (0 : H) 1

/-- A point `x` satisfies the symmetric second-difference bound `ε` when some positive step size
controls the unit-sphere symmetric second-difference quotients strictly below `ε`. -/
noncomputable def HasSymmetricSecondDifferenceBound
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) : Prop :=
  ∃ η : Set.Ioi (0 : ℝ),
    sSup (symmetricSecondDifferenceQuotientSet f x η) < ((ε : ℝ) : EReal)

/-- Unfolding `HasSymmetricSecondDifferenceBound` yields the symmetric second-difference quotient
sublevel condition. -/
theorem hasSymmetricSecondDifferenceBound_iff
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) :
    HasSymmetricSecondDifferenceBound f x ε ↔
      ∃ η : Set.Ioi (0 : ℝ),
        sSup (symmetricSecondDifferenceQuotientSet f x η) < ((ε : ℝ) : EReal) :=
  Iff.rfl

/-- The symmetric second-difference bound is equivalent to the source-facing pointwise unit-sphere
estimate. -/
theorem hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere
    (f : H → Set.Ioi (⊥ : EReal)) (x : H) (ε : Set.Ioi (0 : ℝ)) :
    HasSymmetricSecondDifferenceBound f x ε ↔
      ∃ η : Set.Ioi (0 : ℝ), ∀ y ∈ Metric.sphere (0 : H) 1,
        (f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal) <
          ((((η : ℝ) * (ε : ℝ) : ℝ) : EReal)) := sorry

end SymmetricSecondDifferences

section EkelandLebourgTheorem

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

-- Proof sketch: for the forward implication, `x ∈ cont f` supplies a ball on which the
-- finite-valued representative is an ambient convex real function, so Fréchet differentiability at
-- `x` gives a first-order expansion whose error is `o (‖h‖)`; evaluating it at `h = ± η y` and
-- adding cancels the linear part and yields the source-facing symmetric second-difference estimate
-- for every unit vector `y`. For the reverse implication, Proposition 16.17 applies at the
-- Chapter 16 bridge point `ContinuousAtOnEffectiveDomain.of_mem_cont hxcont` to provide a
-- subgradient at `x`; combine the subgradient inequality with the symmetric estimate and the
-- secant-slope monotonicity theorem in the radial direction to obtain the uniform little-o
-- remainder required for Fréchet differentiability.
/-- Proposition 18.1: for a convex `]-∞,+∞]`-valued function on a real Hilbert space, ambient
continuity at `x` in the source sense `x ∈ cont f` is equivalent to Fréchet differentiability of
the finite-valued representative at `x` together with the source symmetric second-difference
estimate at every positive tolerance. -/
theorem differentiableAt_toReal_iff_forall_pos_exists_pos_symmetricSecondDifference_lt
    (f : H → Set.Ioi (⊥ : EReal)) (hconv : ConvexOn f (effectiveDomain f))
    {x : H} (hxcont : x ∈ cont f) :
    DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔
      ∀ ε : Set.Ioi (0 : ℝ), ∃ η : Set.Ioi (0 : ℝ), ∀ y : H, ‖y‖ = 1 →
        (f (x + (η : ℝ) • y) : EReal) + (f (x - (η : ℝ) • y) : EReal) -
            2 * (f x : EReal) <
          (((η : ℝ) * (ε : ℝ) : ℝ) : EReal) := by
  simpa [hasSymmetricSecondDifferenceBound_iff_forall_mem_sphere, mem_sphere_zero_iff_norm] using
    (show
      DifferentiableAt ℝ (fun y ↦ (f y : EReal).toReal) x ↔
        ∀ ε : Set.Ioi (0 : ℝ), HasSymmetricSecondDifferenceBound f x ε from
      sorry)

end EkelandLebourgTheorem

end ERealFunction
