/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@5bf5af722d85bd5c98368c41c4066124a15e8fd3:ReasBook/Papers/TR_LALM_theory/README.md (formalization contributor).
-/

module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TR_LALM_theory.Algorithm_2_1.Iteration

public section

open scoped LALM

namespace LALM

variable {n m : ℕ}

/-- The Hilbert space of a primal point, multiplier, and preceding primal step
used in the Kurdyka--Łojasiewicz analysis of LALM. -/
abbrev LiftedState (n m : ℕ) :=
  WithLp 2 (EuclideanSpace ℝ (Fin n) ×
    WithLp 2 (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin n)))

/-- Assemble a primal point, multiplier, and preceding step into a lifted LALM
state. -/
@[expose] def liftedState (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m))
    (step : EuclideanSpace ℝ (Fin n)) : LiftedState n m :=
  WithLp.toLp 2 (x, WithLp.toLp 2 (multiplier, step))

/-- The primal-point coordinate of a lifted state assembled by `liftedState`. -/
@[simp] theorem liftedState_point (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (step : EuclideanSpace ℝ (Fin n)) :
    (liftedState x multiplier step).fst = x := rfl

/-- The multiplier coordinate of a lifted state assembled by `liftedState`. -/
@[simp] theorem liftedState_multiplier (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (step : EuclideanSpace ℝ (Fin n)) :
    (liftedState x multiplier step).snd.fst = multiplier := rfl

/-- The preceding-step coordinate of a lifted state assembled by `liftedState`. -/
@[simp] theorem liftedState_step (x : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) (step : EuclideanSpace ℝ (Fin n)) :
    (liftedState x multiplier step).snd.snd = step := rfl

/-- The lifted LALM energy is the augmented Lagrangian plus the quadratic
correction in the preceding primal step. -/
@[expose] noncomputable def liftedEnergy
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) : LiftedState n m → ℝ :=
  fun u ↦ ℒ[f, c; ρ](u.fst, u.snd.fst) + (β / 4) * ‖u.snd.snd‖ ^ 2

/-- The lifted energy evaluated at a lifted state has the source formula. -/
@[simp] theorem liftedEnergy_liftedState
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m))
    (ρ β : ℝ) (x step : EuclideanSpace ℝ (Fin n))
    (multiplier : EuclideanSpace ℝ (Fin m)) :
    liftedEnergy f c ρ β (liftedState x multiplier step) =
      ℒ[f, c; ρ](x, multiplier) + (β / 4) * ‖step‖ ^ 2 := rfl

namespace Run

variable {f : EuclideanSpace ℝ (Fin n) → ℝ}
variable {c : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m)}
variable {x₀ : EuclideanSpace ℝ (Fin n)}
variable {multiplier₀ : EuclideanSpace ℝ (Fin m)}
variable {ρ β : ℝ}

/-- The lifted iterate stores the current point and multiplier together with the
preceding primal step, using `k - 1` also at the harmless initial index. -/
@[expose] def liftedIterate (run : Run f c ρ β x₀ multiplier₀) : ℕ → LiftedState n m :=
  fun k ↦ liftedState (run.point k) (run.multiplier k) (run.step (k - 1))

/-- A lifted iterate exposes its point, multiplier, and preceding-step
coordinates. -/
@[simp] theorem liftedIterate_apply (run : Run f c ρ β x₀ multiplier₀) (k : ℕ) :
    run.liftedIterate k =
      liftedState (run.point k) (run.multiplier k) (run.step (k - 1)) := rfl

end Run

end LALM

end
