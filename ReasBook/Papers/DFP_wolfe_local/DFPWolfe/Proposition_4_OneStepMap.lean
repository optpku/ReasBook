/-
Copyright (c) 2026 Zichen Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang
-/
module

public import ReasLib.Optimization.DFP.AbstractSecantStep.ExactUpdate

/-!
# Proposition 4: exact one-step map

Paper label: `prop:one-step` in `main-new.tex`.

Write `v = Hg`, `δ = gᵀHg`, `w = Av`, `β = vᵀAv`, and `γ = wᵀHw`.
The abstract secant step satisfies `g₊ = g - τ(δ / β)w` and
`H₊ = H - (Hw)(Hw)ᵀ / γ + vvᵀ / β`. The matrix update is independent
of `τ`, and the denominators `β` and `γ` are positive.

The proofs are in `AbstractSecantStep` and `AbstractSecantStep.ExactUpdate`.
The checks below include the positivity assertions as well as both formulas.
-/

-- Equations `eq:one-step-g` and `eq:one-step-H`.
#check DFP.AbstractSecantStep.nextGradient_formula
#check DFP.AbstractSecantStep.nextInverseHessian_formula
#check DFP.AbstractSecantStep.nextInverseHessian_tau_independent

-- Positivity of β and γ, respectively.
#check DFP.AbstractSecantStep.preconditionedEnergy_pos
#check DFP.AbstractSecantStep.secantImageEnergy_pos
