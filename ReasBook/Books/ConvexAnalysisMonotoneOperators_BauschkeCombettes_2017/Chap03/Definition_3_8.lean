/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Tactic.Recall
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_8

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {X : Type u} [PseudoMetricSpace X]

/- The textbook distance `d_C(x)` is formalized by the canonical metric-space
distance-to-a-set function `Metric.infDist x C`. -/
recall Metric.infDist

/-- Definition 3.8: a point `p` is a best approximation to `x` from `C` when it lies in `C` and
realizes the distance from `x` to `C`. -/
abbrev IsBestApproximation (x : X) (C : Set X) (p : X) : Prop :=
  p ∈ C ∧ dist x p = Metric.infDist x C

/-- Definition 3.8: the set-valued projector onto `C` sends `x` to the set of best
approximations to `x` from `C`. -/
def setValuedProjector (C : Set X) : SetValuedOperator X X :=
  fun x ↦ {p | IsBestApproximation x C p}

/- The textbook set-valued projector onto `C` is written `P[C]`. -/
notation "P[" C "]" => setValuedProjector C

/-- Membership in the set-valued projector is exactly the best-approximation property. -/
@[simp] theorem mem_setValuedProjector_iff {C : Set X} {x p : X} :
    p ∈ P[C] x ↔ IsBestApproximation x C p :=
  Iff.rfl

/-- A best approximation is exactly a point of `C` whose distance to `x`
equals `Metric.infDist x C`. -/
@[simp] theorem isBestApproximation_iff_mem_and_dist_eq_infDist (x : X) (C : Set X) (p : X) :
    IsBestApproximation x C p ↔ p ∈ C ∧ dist x p = Metric.infDist x C :=
  Iff.rfl

/-- Definition 3.8: a set is proximinal when every point of the ambient space has at least one
best approximation in that set. -/
def IsProximinalIn (C : Set X) : Prop :=
  ∀ x : X, ∃ p : X, IsBestApproximation x C p

/-- Compatibility alias for the chapter's earlier `IsProximal` name. -/
abbrev IsProximal (C : Set X) : Prop :=
  IsProximinalIn C

/-- A set is proximinal exactly when each point admits a best approximation from the set. -/
@[simp] theorem isProximinalIn_iff_forall_exists_bestApproximation (C : Set X) :
    IsProximinalIn C ↔ ∀ x : X, ∃ p : X, IsBestApproximation x C p :=
  Iff.rfl

/-- A set is proximinal exactly when every value of its set-valued projector is nonempty. -/
@[simp] theorem isProximinalIn_iff_forall_setValuedProjector_nonempty (C : Set X) :
    IsProximinalIn C ↔ ∀ x : X, (P[C] x).Nonempty := by
  simp [IsProximinalIn, Set.Nonempty]

/-- Compatibility form of `isProximinalIn_iff_forall_exists_bestApproximation`. -/
@[simp] theorem isProximal_iff_forall_exists_bestApproximation (C : Set X) :
    IsProximal C ↔ ∀ x : X, ∃ p : X, IsBestApproximation x C p :=
  isProximinalIn_iff_forall_exists_bestApproximation C

/-- Compatibility form of `isProximinalIn_iff_forall_setValuedProjector_nonempty`. -/
@[simp] theorem isProximal_iff_forall_setValuedProjector_nonempty (C : Set X) :
    IsProximal C ↔ ∀ x : X, (P[C] x).Nonempty :=
  isProximinalIn_iff_forall_setValuedProjector_nonempty C

/-- A set is Chebyshev when every point of the ambient space has a unique best approximation in
that set. -/
def IsChebyshev (C : Set X) : Prop :=
  ∀ x : X, ∃! p : X, IsBestApproximation x C p

/-- A set is Chebyshev exactly when each point admits a unique best approximation from the set. -/
@[simp] theorem isChebyshev_iff_forall_existsUnique_bestApproximation (C : Set X) :
    IsChebyshev C ↔ ∀ x : X, ∃! p : X, IsBestApproximation x C p :=
  Iff.rfl

/-- A set is Chebyshev exactly when each value of its set-valued projector is a singleton. -/
@[simp] theorem isChebyshev_iff_forall_existsUnique_mem_setValuedProjector (C : Set X) :
    IsChebyshev C ↔ ∀ x : X, ∃! p : X, p ∈ P[C] x := by
  simp [IsChebyshev]

/-- For a Chebyshev set, the projection point of `x` onto `C` is the unique best approximation in
the ambient space. -/
noncomputable def projectionPoint (C : Set X) (hC : IsChebyshev C) (x : X) : X :=
  (hC x).choose

/- The textbook metric projection onto a Chebyshev set `C` is written `P[C, hC]`. -/
notation "P[" C ", " hC "]" => projectionPoint C hC

/-- For a Chebyshev set, the chosen projection point belongs to the set-valued projector. -/
@[simp] theorem projectionPoint_mem_setValuedProjector (C : Set X) (hC : IsChebyshev C) (x : X) :
    P[C, hC] x ∈ P[C] x :=
  (hC x).choose_spec.left

/-- The chosen projection point is a best approximation. -/
theorem projectionPoint_isBestApproximation (C : Set X) (hC : IsChebyshev C) (x : X) :
    IsBestApproximation x C (P[C, hC] x) :=
  projectionPoint_mem_setValuedProjector C hC x

/-- The chosen projection point lies in the Chebyshev set. -/
@[simp] theorem projectionPoint_mem (C : Set X) (hC : IsChebyshev C) (x : X) :
    P[C, hC] x ∈ C :=
  (projectionPoint_isBestApproximation C hC x).1

/-- In a Chebyshev set, any best approximation of `x` coincides with the chosen projection point.
-/
theorem eq_projectionPoint_of_isBestApproximation (C : Set X) (hC : IsChebyshev C) {x p : X}
    (hp : IsBestApproximation x C p) : p = P[C, hC] x :=
  (hC x).unique hp (projectionPoint_isBestApproximation C hC x)

/-- For a Chebyshev set, each value of the set-valued projector is the singleton consisting of the
chosen projection point. -/
@[simp] theorem setValuedProjector_eq_singleton_projectionPoint
    (C : Set X) (hC : IsChebyshev C) (x : X) :
    P[C] x = ({P[C, hC] x} : Set X) := by
  ext p
  constructor
  · intro hp
    rw [Set.mem_singleton_iff]
    exact eq_projectionPoint_of_isBestApproximation C hC <|
      mem_setValuedProjector_iff.mp hp
  · intro hp
    rw [Set.mem_singleton_iff] at hp
    rw [hp]
    exact projectionPoint_mem_setValuedProjector C hC x

/-- For a Chebyshev set, the projector is the single-valued specialization of the set-valued
projector, with codomain restricted to `C`. -/
noncomputable def projector (C : Set X) (hC : IsChebyshev C) : X → C :=
  fun x ↦ ⟨P[C, hC] x, projectionPoint_mem C hC x⟩

/-- The value of the projector is a best approximation to the original point. -/
theorem projector_isBestApproximation (C : Set X) (hC : IsChebyshev C) (x : X) :
    IsBestApproximation x C (projector C hC x : X) :=
  projectionPoint_isBestApproximation C hC x
