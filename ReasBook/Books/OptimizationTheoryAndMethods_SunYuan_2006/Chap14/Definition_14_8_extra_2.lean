/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Order.Filter.Extr
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_1
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.LocallyLipschitzAt

noncomputable section

open Filter

section

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "JacobianMap" => X →L[ℝ] Y

-- Domain sampling pass:
-- * primary domain: semismoothness of locally Lipschitz maps `F : X → Y`
-- * core/canonical owner reused from the chapter: `generalizedJacobian F x : Set JacobianMap`
--   from `Definition_14_8_extra_1`
-- * primitive data in this file: the semismooth linearization limit/filter surface built from
--   that owner, together with the shared Chapter 14 owner `LocallyLipschitzAt`
-- * derived API in this file: `SemismoothAt`, its unfolding theorem, and the common-limit
--   consequence for difference quotients

open scoped GeneralizedJacobian

/-- The joint filter encoding `V ∈ ∂ F (x + t • h')`, `h' → h`, and `t ↓ 0` for the chapter-level
generalized Jacobian owner `∂ F`. -/
def semismoothSelectionFilter
    (F : X → Y) (x h : X) : Filter (JacobianMap × X × ℝ) :=
  principal {p | p.1 ∈ (∂ F) (x + p.2.2 • p.2.1)} ⊓
    comap (fun p : JacobianMap × X × ℝ ↦ (p.2.1, p.2.2))
      (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0))

/-- The source quantity `V h'` attached to a generalized Jacobian element `V` and perturbed
direction `h'`. -/
def semismoothLinearization (p : JacobianMap × X × ℝ) : Y :=
  p.1 p.2.1

/-- `hasSemismoothLinearizationLimit F x h l` states that the source limit
`lim_{V ∈ ∂ F (x + t • h'), h' → h, t ↓ 0} V h'` exists and equals `l`. -/
def hasSemismoothLinearizationLimit
    (F : X → Y) (x h : X) (l : Y) : Prop :=
  Tendsto semismoothLinearization (semismoothSelectionFilter F x h) (nhds l)

/-- Unfolding formula for `hasSemismoothLinearizationLimit`. -/
theorem hasSemismoothLinearizationLimit_iff
    {F : X → Y} {x h : X} {l : Y} :
    hasSemismoothLinearizationLimit F x h l ↔
      Tendsto semismoothLinearization (semismoothSelectionFilter F x h) (nhds l) :=
  Iff.rfl

/-- The difference quotient `(F (x + t • h') - F x) / t`, written in Lean as
`(1 / t) • (F (x + t • h') - F x)`. -/
def semismoothDifferenceQuotient
    (F : X → Y) (x : X) (p : X × ℝ) : Y :=
  (1 / p.2) • (F (x + p.2 • p.1) - F x)

/-- Evaluating `semismoothDifferenceQuotient F x` on `(h', t)` gives the source difference
quotient `(1 / t) • (F (x + t • h') - F x)`. -/
theorem semismoothDifferenceQuotient_apply
    (F : X → Y) (x : X) (h' : X) (t : ℝ) :
    semismoothDifferenceQuotient F x (h', t) = (1 / t) • (F (x + t • h') - F x) :=
  rfl

/-- Chapter14 Definition 14.8-extra-2 (1): `F` is semismooth at `x` when it is locally
Lipschitz there and, for every direction `h`, the limit
`lim_{V ∈ ∂ F (x + t • h'), h' → h, t ↓ 0} V h'` exists, where
`∂ F` is the source generalized Jacobian. -/
class SemismoothAt (F : X → Y) (x : X) : Prop
    extends LocallyLipschitzAt F x where
  /-- For every direction `h`, the generalized Jacobian evaluations `V h'` converge along the
  source joint limit `V ∈ ∂ F (x + t • h')`, `h' → h`, `t ↓ 0`. -/
  exists_linearization_limit :
    ∀ h : X, ∃ l : Y, hasSemismoothLinearizationLimit F x h l

/-- `SemismoothAt F x` is proposition-valued. -/
instance semismoothAt_subsingleton (F : X → Y) (x : X) :
    Subsingleton (SemismoothAt F x) := inferInstance

/-- Unfolding formula for `SemismoothAt`. -/
theorem semismoothAt_iff {F : X → Y} {x : X} :
    SemismoothAt F x ↔
      LocallyLipschitzAt F x ∧
        ∀ h : X, ∃ l : Y, hasSemismoothLinearizationLimit F x h l := by
  constructor
  · intro h
    exact ⟨h.toLocallyLipschitzAt, h.exists_linearization_limit⟩
  · rintro ⟨h_local, h_limit⟩
    exact
      { toLocallyLipschitzAt := h_local
        exists_linearization_limit := h_limit }

/-- Chapter14 Definition 14.8-extra-2 (2): if `F` is semismooth at `x`, then for every
direction `h` there is a common limit `l` such that both the generalized Jacobian values
`V h'` with `V ∈ ∂ F (x + t • h')`, `h' → h`, `t ↓ 0` and the difference quotients
`(1 / t) • (F (x + t • h') - F x)` converge to `l`. -/
theorem SemismoothAt.existsCommonLimit
    {F : X → Y} {x h : X} (h_semismooth : SemismoothAt F x) :
    ∃ l : Y,
      hasSemismoothLinearizationLimit F x h l ∧
        Tendsto (semismoothDifferenceQuotient F x)
          (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds l) := sorry

#print axioms semismoothSelectionFilter
#print axioms semismoothLinearization
#print axioms hasSemismoothLinearizationLimit
#print axioms semismoothDifferenceQuotient

end
