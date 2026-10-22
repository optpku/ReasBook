/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.OneSidedDirectionalDeriv
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2

noncomputable section

open Asymptotics Filter
open scoped GeneralizedJacobian

section

universe u v

variable {X : Type u} {Y : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup Y] [NormedSpace ℝ Y]

local notation "JacobianMap" => X →L[ℝ] Y

-- Domain sampling pass:
-- * primary domain: Chapter 14 semismoothness for maps `F : X → Y`
-- * core/canonical owners reused from earlier Chapter 14 files:
--   `generalizedJacobian F` from `Definition_14_8_extra_1`,
--   `LocallyLipschitzAt F x` and `SemismoothAt F x` from `Definition_14_8_extra_2`
-- * source-facing owner added in this file: `OrderSemismoothAt F x p`
-- * bridge/view layer added in this file: the order-semismooth remainder filter and remainder
--   estimate built from the canonical generalized-Jacobian owner `∂ F`

/-- The pair filter encoding `V ∈ (∂ F) (x + h)` together with `h → 0` from the
source order-semismoothness condition. -/
def semismoothRemainderFilter
    (F : X → Y) (x : X) :
    Filter (JacobianMap × X) :=
  principal {q | q.1 ∈ (∂ F) (x + q.2)} ⊓
    comap Prod.snd (nhds (0 : X))

/-- The source remainder term `V h - F'(x; h)` evaluated on a pair `(V, h)`. -/
def semismoothRemainder (F : X → Y) (x : X) (q : JacobianMap × X) : Y :=
  q.1 q.2 - oneSidedDirectionalDeriv F x q.2

/-- Evaluating `semismoothRemainder F x` on `(V, h)` gives the source expression
`V h - F'(x; h)`. -/
theorem semismoothRemainder_apply
    (F : X → Y) (x : X) (V : JacobianMap) (h : X) :
    semismoothRemainder F x (V, h) = V h - oneSidedDirectionalDeriv F x h := rfl

/-- Chapter14 Definition 14.8-extra-4 (1): `OrderSemismoothAt F x p` means that `0 < p ≤ 1`,
`F` is semismooth at `x` in the canonical Chapter 14 sense, every direction admits the source
right directional derivative `F'(x; h)` represented by `oneSidedDirectionalDeriv F x h`, and
the remainder `V h - F'(x; h)` with `V ∈ (∂ F) (x + h)` is `O(‖h‖^(1 + p))` as `h → 0`. -/
@[mk_iff orderSemismoothAt_iff]
class OrderSemismoothAt (F : X → Y) (x : X) (p : ℝ) : Prop
    extends SemismoothAt F x where
  /-- Every direction admits the source right directional derivative `F'(x; h)`. -/
  hasOneSidedDirectionalDerivAt :
    ∀ h : X, HasOneSidedDirectionalDerivAt F (oneSidedDirectionalDeriv F x h) x h
  /-- The source order parameter satisfies `0 < p`. -/
  zero_lt_order : 0 < p
  /-- The source order parameter satisfies `p ≤ 1`. -/
  order_le_one : p ≤ 1
  /-- The source remainder estimate `V h - F'(x; h) = O(‖h‖^(1 + p))` as `h → 0` with
  `V ∈ (∂ F) (x + h)`. -/
  isBigO_remainder :
    Asymptotics.IsBigO
      (semismoothRemainderFilter F x)
      (semismoothRemainder F x)
      (fun q : JacobianMap × X ↦ Real.rpow ‖q.2‖ (1 + p))

/-- `OrderSemismoothAt F x p` is proposition-valued. -/
instance orderSemismoothAt_subsingleton (F : X → Y) (x : X) (p : ℝ) :
    Subsingleton (OrderSemismoothAt F x p) := inferInstance

#print axioms oneSidedDirectionalDeriv
#print axioms semismoothRemainderFilter
#print axioms semismoothRemainder

end
