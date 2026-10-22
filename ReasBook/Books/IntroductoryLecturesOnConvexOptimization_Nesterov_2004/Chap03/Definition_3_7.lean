/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.Proposition_2_5

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open WithLp

noncomputable section

namespace EuclideanSpace

/-- The admissible exponents for finite-dimensional `ℓ_p` geometry, namely `1 ≤ p < ∞`. -/
abbrev LpExponent := {q : ENNReal // 1 ≤ q ∧ q ≠ ⊤}

instance (p : LpExponent) : Fact (1 ≤ (p : ENNReal)) :=
  ⟨p.2.1⟩

namespace LpExponent

/-- The real exponent attached to an admissible `ℓ_p` exponent. -/
abbrev toReal (p : EuclideanSpace.LpExponent) : ℝ :=
  ((p : ENNReal).toReal)

theorem toReal_pos (p : EuclideanSpace.LpExponent) : 0 < p.toReal :=
  ENNReal.toReal_pos_iff.mpr
    ⟨lt_of_lt_of_le zero_lt_one p.2.1, lt_of_le_of_ne le_top p.2.2⟩

end LpExponent

private abbrev coordinateLpEquiv (n : ℕ) (p : LpExponent) :
    EuclideanSpace ℝ (Fin n) ≃ₗ[ℝ] WithLp (p : ENNReal) (Fin n → ℝ) :=
  (EuclideanSpace.equiv (Fin n) ℝ).toLinearEquiv.trans
    (WithLp.linearEquiv (p : ENNReal) ℝ (Fin n → ℝ)).symm

instance : One LpExponent where
  one := ⟨(1 : ENNReal), by constructor <;> simp⟩

namespace LpExponent

@[simp] theorem one_toReal : (1 : EuclideanSpace.LpExponent).toReal = 1 := by
  change (1 : ENNReal).toReal = 1
  exact ENNReal.toReal_one

end LpExponent

/- Definition 3.7 is source-facing in the chapter's finite-dimensional `ℓ_p`-geometry domain.

Sampled owner-style declarations:
- `EuclideanSpace.l1Seminorm`
- `EuclideanSpace.linftyNorm`
- `PiLp.norm_eq_sum`
- `Seminorm.closedBall`

Best owner abstraction:
- the coordinate pullback seminorm
  `EuclideanSpace.lpSeminorm n p : Seminorm ℝ (EuclideanSpace ℝ (Fin n))`

Primitive data:
- the ambient dimension `n : ℕ`
- the exponent `p : LpExponent`

Derived API:
- the textbook evaluation notation `‖x‖_[p]`
- the raw coordinate formula `lpSeminorm_apply`
- the notation-facing coordinate formula `lpNorm_eq_sum`
- the induced normed-seminorm instance `lpSeminorm_isNorm`
- the `p = 1` bridge `lpSeminorm_one_eq_l1Seminorm`
- the `p = 1` coordinate specialization `lpSeminorm_one_apply`
- the downstream textbook `ℓ_p` ball `(EuclideanSpace.lpSeminorm n p).closedBall x₀ r`, obtained
  directly from
  `Seminorm.closedBall`

Source/core/bridge triage:
- source-facing: `EuclideanSpace.lpSeminorm n p`
- core/canonical: `Seminorm.comp (normSeminorm ℝ (WithLp (p : ENNReal) (Fin n → ℝ)))
  (coordinateLpEquiv n p).toLinearMap`
- bridge/view: the notation `‖x‖_[p]`, `lpSeminorm_isNorm`, `lpSeminorm_apply`,
  `lpNorm_eq_sum`, `lpSeminorm_one_eq_l1Seminorm`, `lpSeminorm_one_apply`

The former `lpNorm`/`lpBall` API duplicated owner declarations that are already canonical at the
seminorm layer, so this file keeps only the ambient owner `EuclideanSpace.lpSeminorm`, aligns its
public surface with the existing `EuclideanSpace.l1Seminorm` and `EuclideanSpace.linftyNorm`
owners, bridges its `p = 1` specialization to `EuclideanSpace.l1Seminorm`, records the
source-facing zero-detection fact via `lpSeminorm_isNorm`, and uses `Seminorm.closedBall`
directly for the textbook ball while exposing the recurring pointwise surface through `‖x‖_[p]`.
-/

/-- Definition 3.7: the coordinate `ℓ_p` seminorm on `ℝ^n`, obtained by pulling back the owner
`L^p` norm on `WithLp (p : ENNReal) (Fin n → ℝ)` along the Euclidean coordinate map. The induced
`Seminorm.IsNorm` instance recovers the textbook norm property, its value on a vector is written
`‖x‖_[p]` below, and its closed balls are the textbook `ℓ_p` balls. -/
def lpSeminorm (n : ℕ) (p : LpExponent) : Seminorm ℝ (EuclideanSpace ℝ (Fin n)) :=
  Seminorm.comp
    (normSeminorm ℝ (WithLp (p : ENNReal) (Fin n → ℝ)))
    (coordinateLpEquiv n p).toLinearMap

end EuclideanSpace

namespace EuclideanSpaceLp

scoped notation:max "‖" x "‖_[" p "]" => EuclideanSpace.lpSeminorm _ p x

end EuclideanSpaceLp

open scoped EuclideanSpaceLp

namespace EuclideanSpace

section

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin n)

private theorem lpSeminorm_toLp (x : E) (p : LpExponent) :
    lpSeminorm n p x = ‖toLp (p : ENNReal) (fun i ↦ x i)‖ := by
  change ‖coordinateLpEquiv n p x‖ = _
  rfl

/-- The canonical coordinate `ℓ_p` seminorm is a norm on `ℝⁿ`. -/
-- Proof sketch: `lpSeminorm` is the pullback of the owner norm on
-- `WithLp (p : ENNReal) (Fin n → ℝ)`
-- along the coordinate linear equivalence defining `lpSeminorm`, so vanishing forces the vector
-- itself to vanish.
instance lpSeminorm_isNorm (p : LpExponent) : Seminorm.IsNorm (lpSeminorm n p : Seminorm ℝ E) where
  eq_zero_of_map_eq_zero := by
    intro x hx
    exact (coordinateLpEquiv n p).map_eq_zero_iff.mp <|
      norm_eq_zero.mp <| by
        simpa [lpSeminorm, coordinateLpEquiv] using hx

/-- Applying the canonical coordinate `ℓ_p` seminorm to a vector gives the usual coordinate
formula. -/
-- Proof sketch: rewrite `lpSeminorm p x` as the owner `WithLp` norm on the coordinate function
-- `fun i ↦ x i` and apply `PiLp.norm_eq_sum`.
theorem lpSeminorm_apply (x : E) (p : LpExponent) :
    lpSeminorm n p x = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal : ℝ) := by
  rw [lpSeminorm_toLp x p]
  simpa [Real.norm_eq_abs] using PiLp.norm_eq_sum p.toReal_pos (toLp (p : ENNReal) fun i ↦ x i)

/-- The textbook `ℓ_p` notation on `EuclideanSpace ℝ (Fin n)` is given by the coordinate formula
for the owner seminorm `EuclideanSpace.lpSeminorm`. -/
theorem lpNorm_eq_sum (x : E) (p : LpExponent) :
    ‖x‖_[p] = (∑ i, |x i| ^ p.toReal) ^ (1 / p.toReal : ℝ) := by
  simpa using lpSeminorm_apply x p

/-- The `p = 1` specialization of `lpSeminorm_apply` recovers the earlier project coordinate
formula for `l1Seminorm`. -/
theorem lpSeminorm_one_apply (x : E) :
    ‖x‖_[(1 : LpExponent)] = ∑ i, ‖x i‖ := by
  rw [lpNorm_eq_sum x (1 : LpExponent), LpExponent.one_toReal]
  norm_num

/-- The `p = 1` specialization of `lpSeminorm` coincides with the earlier project owner
`l1Seminorm`. -/
theorem lpSeminorm_one_eq_l1Seminorm :
    lpSeminorm n (1 : LpExponent) = l1Seminorm n := by
  ext x
  rw [l1Seminorm_apply]
  simpa using lpSeminorm_one_apply x

end

end EuclideanSpace
