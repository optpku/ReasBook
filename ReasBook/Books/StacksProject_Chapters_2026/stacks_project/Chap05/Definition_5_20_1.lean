module

public import Mathlib.Order.Grade
public import Mathlib.Topology.Specialization
public import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open Specialization TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for dimension functions on topological spaces:
- source-facing specialization relation: `Specializes`
- core order owner for immediate steps: `CovBy` on `Specialization X`
- core graded-order owner: `GradeOrder ℤ (Specialization X)`

Layer triage:
- `source-facing`: `IsImmediateSpecialization` and `IsDimensionFunction`
- `core/canonical`: `CovBy` and `GradeOrder` on the specialization order
- `bridge/view`: under `T₀`, immediate specializations are exactly covers in `Specialization X`;
  a dimension function forces `T₀` and canonically grades `Specialization X`

Primitive data is only the strict-decrease and unit-drop axioms. The induced `T₀` separation and
the order-theoretic cover interface are derived API, so they should not be stored as primitive
fields.
-/

/-- A point `y` is an immediate specialization of `x` if `y` is a proper specialization of `x`
and there is no third point strictly between them in the specialization relation. -/
def IsImmediateSpecialization (x y : X) : Prop :=
  x ⤳ y ∧ x ≠ y ∧ ∀ ⦃z : X⦄, x ⤳ z → z ⤳ y → z = x ∨ z = y

theorem IsImmediateSpecialization.specializes {x y : X} (h : IsImmediateSpecialization x y) :
    x ⤳ y :=
  h.1

theorem IsImmediateSpecialization.ne {x y : X} (h : IsImmediateSpecialization x y) :
    x ≠ y :=
  h.2.1

theorem IsImmediateSpecialization.eq_or_eq {x y z : X} (h : IsImmediateSpecialization x y)
    (hxz : x ⤳ z) (hzy : z ⤳ y) : z = x ∨ z = y :=
  h.2.2 hxz hzy

/-- On a `T₀` space, immediate specializations are exactly cover relations in the canonical
specialization order. -/
theorem isImmediateSpecialization_iff_covBy [T0Space X] {x y : X} :
    IsImmediateSpecialization x y ↔ toEquiv y ⋖ toEquiv x := by
  rw [covBy_iff_lt_and_eq_or_eq]
  constructor
  · intro h
    rcases h with ⟨hxy, hne, hmid⟩
    refine ⟨?_, ?_⟩
    · refine ⟨hxy, ?_⟩
      intro hyx
      exact hne ((hxy.antisymm hyx).eq)
    · intro z hyz hzx
      have hxz : x ⤳ ofEquiv z := by
        simpa using hzx
      have hzy : ofEquiv z ⤳ y := by
        simpa using hyz
      simpa [toEquiv_inj, or_comm] using hmid hxz hzy
  · intro h
    refine ⟨h.1.1, ?_, ?_⟩
    · intro hxy
      exact h.1.2 (by simpa [hxy] using (specializes_rfl : x ⤳ x))
    · intro z hxz hzy
      have hyz : toEquiv y ≤ toEquiv z := by
        simpa using hzy
      have hzx : toEquiv z ≤ toEquiv x := by
        simpa using hxz
      simpa [toEquiv_inj, or_comm] using h.2 (toEquiv z) hyz hzx

/-- Definition 5.20.1: a dimension function on a topological space is an integer-valued function
that is strictly decreasing under proper specialization and drops by exactly one along immediate
specializations. -/
class IsDimensionFunction (δ : X → ℤ) : Prop where
  /-- A dimension function strictly decreases along proper specializations. -/
  strict_of_specializes {x y : X} : x ⤳ y → x ≠ y → δ x > δ y
  /-- A dimension function drops by exactly one along immediate specializations. -/
  eq_add_one_of_immediateSpecialization {x y : X} :
    IsImmediateSpecialization x y → δ x = δ y + 1

/-- A dimension function forces the ambient space to be `T₀`: distinct inseparable points would
make the strict specialization inequality run in both directions. -/
theorem IsDimensionFunction.t0Space {δ : X → ℤ} (hδ : IsDimensionFunction δ) : T0Space X := by
  refine ⟨?_⟩
  intro x y hxy
  by_contra hne
  have hgt : δ x > δ y := hδ.strict_of_specializes hxy.specializes hne
  have hlt : δ y > δ x := hδ.strict_of_specializes hxy.specializes' (fun h ↦ hne h.symm)
  exact lt_irrefl _ (lt_trans hgt hlt)

/-- A dimension function canonically upgrades the specialization order to a graded order. -/
@[reducible] protected noncomputable def IsDimensionFunction.gradeOrder {δ : X → ℤ}
    (hδ : IsDimensionFunction δ) : GradeOrder ℤ (Specialization X) :=
  letI : GradeBoundedOrder ℤ ℤ := Preorder.toGradeBoundedOrder
  GradeOrder.liftRight (δ ∘ ofEquiv)
    (by
      intro a b hab
      exact hδ.strict_of_specializes (by simpa using hab.le) (by
        intro h
        exact hab.ne <| by simpa [eq_comm] using h))
    (by
      intro a b hab
      letI : T0Space X := hδ.t0Space
      have himm : IsImmediateSpecialization (ofEquiv b) (ofEquiv a) :=
        (isImmediateSpecialization_iff_covBy).2 <| by simpa using hab
      rw [Order.covBy_iff_add_one_eq]
      simpa [eq_comm] using hδ.eq_add_one_of_immediateSpecialization himm)

/-- On a `T1` space, the constant zero function is a dimension function because there are no
proper specializations. -/
instance [T1Space X] : IsDimensionFunction (fun _ : X ↦ (0 : ℤ)) where
  strict_of_specializes := by
    intro x y hxy hne
    exact (hne (Specializes.eq hxy)).elim
  eq_add_one_of_immediateSpecialization := by
    intro x y hxy
    exact (hxy.ne (Specializes.eq hxy.specializes)).elim
