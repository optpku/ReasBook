/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap25.Theorem_25_30

noncomputable section

namespace ProbabilityTheory

variable {d : ℕ}

/-- The time derivative `∂ₜ F` of a function on `ℝ^d × ℝ`, taken in the last coordinate. -/
noncomputable def timePartialDeriv
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ) :
    EuclideanSpace ℝ (Fin d) × ℝ → ℝ :=
  fun xt ↦ deriv (fun s : ℝ ↦ F (xt.1, s)) xt.2

notation:max "∂ₜ " F:arg => timePartialDeriv F

-- Proof sketch: unfold `timePartialDeriv`; it is the one-variable derivative in the time slot
-- with the spatial variable frozen.
/-- Evaluating `(∂ₜ F)` at `(x,t)` gives the derivative of `s ↦ F(x,s)` at `t`. -/
theorem timePartialDeriv_def
    (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ)
    (xt : EuclideanSpace ℝ (Fin d) × ℝ) :
    (∂ₜ F) xt =
      deriv (fun s : ℝ ↦ F (xt.1, s)) xt.2 := by
  -- Proof comment: `timePartialDeriv` is defined by freezing the spatial coordinate and taking
  -- the one-variable derivative in time.
  rfl

/-- The source-facing `C^{2,1}` regularity assumption on `F : ℝ^d × ℝ → ℝ`: the named time and
spatial derivatives are genuine derivatives of the corresponding one-variable slices, and these
derivatives are continuous. The spatial derivatives are expressed through the chapter’s canonical
coordinate-derivative owners `∂ₜ`, `∂[i]`, and `∂²[i,j]` applied to the relevant frozen slices
`x ↦ F (x, t)`. Continuity of `F` itself is derived from this first-order regularity data, so it
is not stored as a primitive field. -/
@[mk_iff isTimeSpaceC21_iff]
class IsTimeSpaceC21 (F : EuclideanSpace ℝ (Fin d) × ℝ → ℝ) : Prop where
  hasDerivAt_time (xt : EuclideanSpace ℝ (Fin d) × ℝ) :
    HasDerivAt (fun s : ℝ ↦ F (xt.1, s)) ((∂ₜ F) xt) xt.2
  continuous_timePartialDeriv : Continuous (∂ₜ F)
  hasDerivAt_space (i : Fin d) (xt : EuclideanSpace ℝ (Fin d) × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦ F (xt.1 + EuclideanSpace.single i (s - xt.1 i), xt.2))
      ((∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2)) xt.1)
      (xt.1 i)
  continuous_spacePartialDeriv (i : Fin d) :
    Continuous
      (fun xt : EuclideanSpace ℝ (Fin d) × ℝ ↦
        (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2)) xt.1)
  hasDerivAt_spaceSecond
      (i j : Fin d) (xt : EuclideanSpace ℝ (Fin d) × ℝ) :
    HasDerivAt
      (fun s : ℝ ↦
        (∂[i] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2))
          (xt.1 + EuclideanSpace.single j (s - xt.1 j)))
      ((∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2)) xt.1)
      (xt.1 j)
  continuous_spaceSecondPartialDeriv (i j : Fin d) :
    Continuous
      (fun xt : EuclideanSpace ℝ (Fin d) × ℝ ↦
        (∂²[i, j] fun x : EuclideanSpace ℝ (Fin d) ↦ F (x, xt.2)) xt.1)

end ProbabilityTheory
