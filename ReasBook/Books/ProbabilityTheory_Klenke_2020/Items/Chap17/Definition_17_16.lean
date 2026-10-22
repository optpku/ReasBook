/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {E : Type u}

/-- Definition 17.16: a matrix `p : E → E → ℝ≥0∞` is a stochastic matrix on `E` if each row has
total mass `1`. Since the codomain is `ℝ≥0∞`, nonnegativity of the entries is built into the
type. Downstream, this source-facing row-sum condition is fed into the canonical discrete kernel
owner `discreteMatrixKernel p`. -/
def IsStochasticMatrix (p : E → E → ℝ≥0∞) : Prop :=
  ∀ x : E, ∑' y : E, p x y = 1

section TranslationInvariantStepMatrix

variable [AddCommGroup E] [MeasurableSpace E] [DiscreteMeasurableSpace E] [MeasurableAdd₂ E]

/-- A step matrix on an additive state space is translation invariant when the one-step law
depends only on the increment `y - x`. -/
def IsTranslationInvariantStepMatrix (p : E → E → ℝ≥0∞) : Prop :=
  ∀ x y : E, p x y = p 0 (y - x)

-- Proof sketch: apply the translation-invariance identity to the target state `x + z`; in an
-- additive commutative group the increment from `x` to `x + z` is exactly `z`.
/-- For a translation-invariant step matrix, the probability of the increment `z` from `x` is the
same as the probability of the same increment from the origin. -/
theorem isTranslationInvariantStepMatrix_apply_add
    {p : E → E → ℝ≥0∞} (h : IsTranslationInvariantStepMatrix p) (x z : E) :
    p x (x + z) = p 0 z := by
  -- Specialize the translation-invariance identity at the endpoint `x + z`.
  have hstep : p x (x + z) = p 0 ((x + z) - x) := h x (x + z)
  -- Normalize the increment from `x` to `x + z` to the displacement `z`.
  simpa using hstep

end TranslationInvariantStepMatrix

section RandomMappingConstruction

variable {Ω : Type v}

/-- The recursive chain obtained by iterating the random self-maps `R n` from the initial state
`x`. This is the source-facing construction `X⁽ˣ⁾_0 = x`,
`X⁽ˣ⁾_{n+1} = R_n (X⁽ˣ⁾_n)`. -/
def stochasticMatrixTrajectory (R : ℕ → Ω → E → E) (x : E) : ℕ → Ω → E
  | 0 => fun _ ↦ x
  | n + 1 => fun ω ↦ R n ω (stochasticMatrixTrajectory R x n ω)

-- Proof sketch: unfold the recursive definition of `stochasticMatrixTrajectory` at time `0`.
/-- The chain driven by the random maps `R` starts from the deterministic initial state `x`. -/
theorem stochasticMatrixTrajectory_zero (R : ℕ → Ω → E → E) (x : E) :
    stochasticMatrixTrajectory R x 0 = fun _ ↦ x := rfl

-- Proof sketch: unfold the recursive definition at time `n + 1`; the next state is obtained by
-- applying the random map `R n` to the current state at time `n`.
/-- The recursive step of the random-mapping construction. -/
theorem stochasticMatrixTrajectory_succ (R : ℕ → Ω → E → E) (x : E) (n : ℕ) :
    stochasticMatrixTrajectory R x (n + 1) =
      fun ω ↦ R n ω (stochasticMatrixTrajectory R x n ω) := rfl

section PathLaw

variable [MeasurableSpace Ω] [MeasurableSpace E]

/-- The path law `Pₓ = 𝓛[X⁽ˣ⁾]` of the random-mapping chain started from `x`. -/
def stochasticMatrixPathLaw (P : ProbabilityMeasure Ω) (R : ℕ → Ω → E → E) (x : E)
    (h_path :
      AEMeasurable (fun ω ↦ fun n ↦ stochasticMatrixTrajectory R x n ω) (P : Measure Ω)) :
    ProbabilityMeasure (ℕ → E) :=
  P.map h_path

-- Proof sketch: `stochasticMatrixPathLaw` is defined as the pushforward of `P` by the path map
-- `ω ↦ (n ↦ X⁽ˣ⁾_n(ω))`, so its underlying measure is exactly that pushforward.
/-- The underlying measure of `stochasticMatrixPathLaw` is the pushforward by the trajectory map. -/
theorem stochasticMatrixPathLaw_toMeasure (P : ProbabilityMeasure Ω) (R : ℕ → Ω → E → E) (x : E)
    (h_path :
      AEMeasurable (fun ω ↦ fun n ↦ stochasticMatrixTrajectory R x n ω) (P : Measure Ω)) :
    (stochasticMatrixPathLaw P R x h_path : Measure (ℕ → E)) =
      (P : Measure Ω).map (fun ω ↦ fun n ↦ stochasticMatrixTrajectory R x n ω) := rfl

end PathLaw
end RandomMappingConstruction
end ProbabilityTheory
