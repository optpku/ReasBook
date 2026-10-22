/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_4
public import Mathlib.Analysis.InnerProductSpace.Adjoint

public section

noncomputable section

universe u v

/-!
Check-only interpretation.

The current repository snapshot still does not contain a checked Chapter 8
owner for the displayed artificial-time diffusion equation
`∂ₜ f = -α • 𝓛(f) f - K⁎ (K f - g)` or a theorem identifying the
lagged-diffusivity right-hand side from Algorithm 8.2.3 with `gradient T`.

Because those source-specific anchors are absent, this file must not invent a
new public ROF/artificial-time-evolution owner or claim that the
lagged-diffusivity clauses from `Book.Ch8.Algorithm_8_2_3.Clauses` are already
exactly `SteepestDescent.iterates`. It therefore keeps the remark as a flat
check-only bridge. The steady-state sentence remains explanatory prose only.
-/

/- Remark 8.2 (1). Main source-facing check-only entry for the displayed
artificial-time diffusion equation
`∂ₜ f = -(α • 𝓛 (f) f) - K⁎ (K f - g)`.

The discrete lagged-diffusivity ingredients already have checked clause owners
in `Book.Ch8.Algorithm_8_2_3.Clauses`, while Exercise 8.4 already provides the
exact fixed-step forward-Euler theorem reused by the remark. What is still
absent is a checked Chapter 8 owner tying those discrete clauses to the
displayed continuous artificial-time diffusion equation, so this file stays as
a thin split `#check` bridge rather than introducing a new theorem or wrapper.

This first `#check` records only the Lean surface of the displayed formula,
with the time derivative, the diffusion operator `𝓛`, the forward operator
`K`, and the adjoint action `K.adjoint` kept as explicit binders. -/
#check
  fun {H : Type u} {G : Type v}
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]
    (timeDerivative : (ℝ → H) → ℝ → H)
    (K : H →L[ℝ] G) (g : G) (α : ℝ)
    (𝓛 : H → H → H) (f : ℝ → H) ↦
    ∀ t : ℝ,
      timeDerivative f t =
        -(α • 𝓛 (f t) (f t)) - K.adjoint (K (f t) - g)

/- Remark 8.2 (2). Source-facing backend check for the fixed-step explicit-time
marching clause after spatial discretization.

Exercise 8.4 already supplies the exact canonical fixed-step forward-Euler
owner. This `#check` records the backend theorem reused by the remark instead
of introducing a new similarity wrapper around Algorithm 8.2.3. -/
#check
  SteepestDescent.forwardEuler_iff_eq_iterates_constStep
