module

public import ReasLib.Analysis.Calculus.ContDiff.AffineCutoffBump

public section

open Set
open scoped ContDiff

noncomputable section

universe u

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The affine cutoff bump formed from `χ`, centered at `x`, with scale `ρ` and
linear coefficient `a`. -/
abbrev affineCutoffBump (χ : E → ℝ) (x : E) (ρ : ℝ) (a : E) : E → ℝ :=
  AffineBump.scaledLinearBump χ x ρ a
