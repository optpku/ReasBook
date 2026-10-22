/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

module

public import OptimizationTheoryAndMethods_SunYuan_2006.Compat

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Order.Filter.Extr

@[expose] public section

noncomputable section

open Filter

universe u

section ConvergenceRates

variable {E : Type u} [NormedAddCommGroup E]

/-- The textbook `R_p` rate formula is defined only for the source cases `p = 1` and `p > 1`. -/
def RRateOrder : Type :=
  { p : ℝ // p = 1 ∨ 1 < p }

namespace RRateOrder

instance : CoeOut RRateOrder ℝ := ⟨Subtype.val⟩

/-- The first-order `R`-rate parameter. -/
def one : RRateOrder :=
  ⟨1, Or.inl rfl⟩

/-- Any real parameter strictly larger than `1` defines a valid higher-order `R`-rate. -/
def ofGtOne (p : ℝ) (hp : 1 < p) : RRateOrder :=
  ⟨p, Or.inr hp⟩

/-- The quadratic `R`-rate parameter. -/
def two : RRateOrder :=
  ofGtOne 2 one_lt_two

instance : OfNat RRateOrder 1 := ⟨one⟩
instance : OfNat RRateOrder 2 := ⟨two⟩

/-- A valid `R`-rate parameter is exactly one of the textbook cases `p = 1` or `p > 1`. -/
theorem eq_one_or_one_lt (p : RRateOrder) : (p : ℝ) = 1 ∨ 1 < (p : ℝ) :=
  p.property

@[simp] theorem coe_one : ((1 : RRateOrder) : ℝ) = 1 := rfl

@[simp] theorem coe_two : ((2 : RRateOrder) : ℝ) = 2 := rfl

end RRateOrder

/-- The exponent sequence used in the textbook `R_p` rate formula for `p = 1` or `p > 1`,
with `k + 1` representing the positive indices in the source notation. -/
def rRateExponent (p : RRateOrder) (k : ℕ) : ℝ :=
  if (p : ℝ) = 1 then
    1 / (k + 1 : ℝ)
  else
    1 / ((p : ℝ) ^ (k + 1 : ℕ))

/-- Evaluating `rRateExponent p k` unfolds the source exponent formula. -/
theorem rRateExponent_eq (p : RRateOrder) (k : ℕ) :
    rRateExponent p k =
      if (p : ℝ) = 1 then 1 / (k + 1 : ℝ) else 1 / ((p : ℝ) ^ (k + 1 : ℕ)) := rfl

/-- For the textbook cases `p = 1` and `p > 1`, the `R`-rate exponents are positive. -/
private theorem rRateExponent_pos (p : RRateOrder) (k : ℕ) :
    0 < rRateExponent p k := by
  rw [rRateExponent_eq]
  split_ifs with hp
  · positivity
  · have hp' : 1 < (p : ℝ) := (RRateOrder.eq_one_or_one_lt p).resolve_left hp
    positivity

/-- The `R`-rate exponents are nonnegative in the two textbook cases `p = 1` and `p > 1`. -/
theorem rRateExponent_nonneg (p : RRateOrder) (k : ℕ) :
    0 ≤ rRateExponent p k :=
  le_of_lt (rRateExponent_pos p k)

/-- For the textbook cases `p = 1` and `p > 1`, `rRate p x xStar` is the source's ordinary real
limsup quantity `R_p`, written with `k + 1` so that Lean's `ℕ`-indexed sequences represent the
positive indices from the source. The convergence predicates below add the source's standing
assumption that `x` converges to `xStar`. -/
def rRate (p : RRateOrder) (x : ℕ → E) (xStar : E) : ℝ :=
  Filter.limsup
    (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent p k))
    atTop

notation "R[" p "]" => rRate p

/-- Unfolding formula for `rRate`. -/
theorem rRate_eq_limsup (p : RRateOrder) (x : ℕ → E) (xStar : E) :
    R[p] x xStar =
      Filter.limsup
        (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent p k))
        atTop := rfl

/-- Since the source defines `R_p` as an ordinary real limsup, `rRate` is already that real
limsup. -/
theorem rRate_eq_ofReal_limsup (p : RRateOrder) (x : ℕ → E) (xStar : E) :
    R[p] x xStar =
      Filter.limsup (fun k ↦ Real.rpow (‖x k - xStar‖) (rRateExponent p k)) atTop := rfl

/-- A sequence is `R`-superlinearly convergent to `xStar` when it converges to `xStar` and
`R[1] x xStar = 0`, matching the source's standing convergence hypothesis. -/
def rSuperlinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ R[1] x xStar = 0

/-- Unfolding formula for `rSuperlinearConvergenceTo`. -/
theorem rSuperlinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rSuperlinearConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ R[1] x xStar = 0 :=
  Iff.rfl

/-- `R`-superlinear convergence includes ordinary convergence to the same limit as part of the
source-facing owner. -/
theorem rSuperlinearConvergenceTo.tendsto
    {x : ℕ → E} {xStar : E} (h : rSuperlinearConvergenceTo x xStar) :
    Tendsto x atTop (nhds xStar) :=
  h.1

/-- Compatibility alias for the source's non-exclusive `R`-linear notion: `R[1] x xStar < 1`
includes both the exact `0 < R₁ < 1` case and the faster `R₁ = 0` case, still under the
source's standing convergence hypothesis. -/
def rAtLeastLinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ R[1] x xStar < 1

/-- Unfolding formula for `rAtLeastLinearConvergenceTo`. -/
theorem rAtLeastLinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rAtLeastLinearConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ R[1] x xStar < 1 :=
  Iff.rfl

/-- A sequence is `R`-linearly convergent to `xStar` when the first `R`-rate lies strictly
between `0` and `1`, excluding the faster `R`-superlinear case, and when `x` converges to
`xStar` as in the source preamble. -/
def rLinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ 0 < R[1] x xStar ∧ R[1] x xStar < 1

/-- The predicate `rLinearConvergenceTo` is proof-irrelevant. -/
instance rLinearConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} :
    Subsingleton (rLinearConvergenceTo x xStar) := inferInstance

/-- Unfolding formula for `rLinearConvergenceTo`. -/
theorem rLinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rLinearConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ 0 < R[1] x xStar ∧ R[1] x xStar < 1 :=
  Iff.rfl

/-- `R`-linear convergence includes ordinary convergence to the same limit as part of the
source-facing owner. -/
theorem rLinearConvergenceTo.tendsto
    {x : ℕ → E} {xStar : E} (h : rLinearConvergenceTo x xStar) :
    Tendsto x atTop (nhds xStar) :=
  h.1

/-- A sequence is `R`-sublinearly convergent to `xStar` when `x` tends to `xStar` and `R₁ = 1`.
-/
class rSublinearConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  /-- The sequence converges to `xStar`. -/
  tendsto : Tendsto x atTop (nhds xStar)
  /-- The first `R`-rate equals `1`. -/
  r1_eq_one : R[1] x xStar = 1

/-- The predicate `rSublinearConvergenceTo` is proof-irrelevant. -/
instance rSublinearConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} :
    Subsingleton (rSublinearConvergenceTo x xStar) := inferInstance

/-- Unfolding formula for `rSublinearConvergenceTo`. -/
theorem rSublinearConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rSublinearConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ R[1] x xStar = 1 := by
  constructor
  · intro h
    exact ⟨h.tendsto, h.r1_eq_one⟩
  · rintro ⟨tendsto, r1_eq_one⟩
    exact ⟨tendsto, r1_eq_one⟩

/-- A sequence is `R`-superquadratically convergent to `xStar` when it converges to `xStar` and
`R[2] x xStar = 0`, matching the source's standing convergence hypothesis. -/
def rSuperquadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ R[2] x xStar = 0

/-- Unfolding formula for `rSuperquadraticConvergenceTo`. -/
theorem rSuperquadraticConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rSuperquadraticConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ R[2] x xStar = 0 :=
  Iff.rfl

/-- `R`-superquadratic convergence includes ordinary convergence to the same limit as part of the
source-facing owner. -/
theorem rSuperquadraticConvergenceTo.tendsto
    {x : ℕ → E} {xStar : E} (h : rSuperquadraticConvergenceTo x xStar) :
    Tendsto x atTop (nhds xStar) :=
  h.1

/-- Compatibility alias for the source's non-exclusive `R`-quadratic notion: `R[2] x xStar < 1`
includes both the exact `0 < R₂ < 1` case and the faster `R₂ = 0` case, still under the
source's standing convergence hypothesis. -/
def rAtLeastQuadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ R[2] x xStar < 1

/-- Unfolding formula for `rAtLeastQuadraticConvergenceTo`. -/
theorem rAtLeastQuadraticConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rAtLeastQuadraticConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ R[2] x xStar < 1 :=
  Iff.rfl

/-- A sequence is `R`-quadratically convergent to `xStar` when the second `R`-rate lies
strictly between `0` and `1`, excluding the faster `R`-superquadratic case, and when `x`
converges to `xStar` as in the source preamble. -/
def rQuadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop :=
  Tendsto x atTop (nhds xStar) ∧ 0 < R[2] x xStar ∧ R[2] x xStar < 1

/-- The predicate `rQuadraticConvergenceTo` is proof-irrelevant. -/
instance rQuadraticConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} :
    Subsingleton (rQuadraticConvergenceTo x xStar) := inferInstance

/-- Unfolding formula for `rQuadraticConvergenceTo`. -/
theorem rQuadraticConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rQuadraticConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ 0 < R[2] x xStar ∧ R[2] x xStar < 1 :=
  Iff.rfl

/-- `R`-quadratic convergence includes ordinary convergence to the same limit as part of the
source-facing owner. -/
theorem rQuadraticConvergenceTo.tendsto
    {x : ℕ → E} {xStar : E} (h : rQuadraticConvergenceTo x xStar) :
    Tendsto x atTop (nhds xStar) :=
  h.1

/-- A sequence is `R`-subquadratically convergent to `xStar` when `x` tends to `xStar` and
`1 ≤ R₂`. -/
class rSubquadraticConvergenceTo (x : ℕ → E) (xStar : E) : Prop where
  /-- The sequence converges to `xStar`. -/
  tendsto : Tendsto x atTop (nhds xStar)
  /-- The second `R`-rate is at least `1`. -/
  one_le_r2 : 1 ≤ R[2] x xStar

/-- The predicate `rSubquadraticConvergenceTo` is proof-irrelevant. -/
instance rSubquadraticConvergenceTo_subsingleton {x : ℕ → E} {xStar : E} :
    Subsingleton (rSubquadraticConvergenceTo x xStar) := inferInstance

/-- Unfolding formula for `rSubquadraticConvergenceTo`. -/
theorem rSubquadraticConvergenceTo_iff (x : ℕ → E) (xStar : E) :
    rSubquadraticConvergenceTo x xStar ↔
      Tendsto x atTop (nhds xStar) ∧ 1 ≤ R[2] x xStar := by
  constructor
  · intro h
    exact ⟨h.tendsto, h.one_le_r2⟩
  · rintro ⟨tendsto, one_le_r2⟩
    exact ⟨tendsto, one_le_r2⟩

end ConvergenceRates
