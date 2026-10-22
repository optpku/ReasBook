/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_5.SmoothNegativeLaplacian
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_27
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Example_2_28
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Prop_8_13.Sobolev
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.MeasureTheory.Function.L2Space

public section

noncomputable section

open scoped BigOperators
open VariationalRegularization

universe u

/-- Helper for Definition 2.4.1-extra-1: the standard Tikhonov penalty on a
real Hilbert space `H₁` is the quadratic functional
`f ↦ (1 / 2 : ℝ) * ‖f‖ ^ 2`. -/
def quadraticPenalty
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] : H → ℝ :=
  fun f ↦ (1 / 2 : ℝ) * ‖f‖ ^ 2

/-- Helper for Definition 2.4.1-extra-1: the defining formula for
`quadraticPenalty`. -/
theorem quadraticPenalty_def
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H) :
    quadraticPenalty f = (1 / 2 : ℝ) * ‖f‖ ^ 2 := by
  -- This companion theorem is just the defining equation of `quadraticPenalty`.
  rfl

/-- Definition 2.4.1-extra-1 (1). The standard Tikhonov penalty functional can
be rewritten in the inner-product form used by operator-style penalties. -/
theorem quadraticPenalty_eq_inner_self
    {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] (f : H) :
    quadraticPenalty f = (1 / 2 : ℝ) * inner ℝ f f := by
  -- First expose the norm-squared form of the quadratic penalty.
  rw [quadraticPenalty_def]
  -- Then convert the norm square to the real inner product with itself.
  rw [← real_inner_self_eq_norm_sq]

/-!
Definition 2.4.1-extra-1. Honest blocker skeleton for the source paragraph on
penalty functionals.

The textbook item combines six clauses: the Hilbert-space quadratic penalty
`(2.46)`, its `L²(Ω)` naming remark, the `H¹` penalty `(2.47)`, the
homogeneous-Neumann / penalty-operator identity `(2.48)`, the diffusion-type
penalty operator `(2.49)`, and the negative-entropy penalty `(2.50)` on an
admissible set `𝒞` from Example 2.27 or Example 2.28.

The current repository snapshot has an exact reusable owner only for the
quadratic clause, plus verified local anchors or analogues for the later
material. This file therefore remains a blocker skeleton rather than a finished
statement formalization: the direct checks below record exact available owners
and honest placeholders for the unresolved `H¹(Ω)`, Neumann/Laplacian,
diffusion, and admissible-entropy surfaces.
-/

/- Definition 2.4.1-extra-1 (1). Source-facing check-only entry for the
standard Tikhonov penalty functional `(2.46)`.

For a real Hilbert space `H₁`, the source formula
`J(f) = (1 / 2 : ℝ) * ‖f‖ ^ 2` is exactly the existing owner
`quadraticPenalty`. -/
#check quadraticPenalty

section

variable {Ω : Type u} [MeasurableSpace Ω]
variable (μ : MeasureTheory.Measure Ω)

/- Definition 2.4.1-extra-1 (2). Source-facing check-only entry for the `L²(Ω)`
naming clause following `(2.46)`.

When `H₁ = L²(Ω)`, the same penalty is the specialization of
`quadraticPenalty` to `MeasureTheory.Lp ℝ 2 μ`. This uses the narrower
canonical `Lp` owner directly rather than importing the currently fragile
Example 2.4 surface. -/
#check (quadraticPenalty : MeasureTheory.Lp ℝ 2 μ → ℝ)

end

/- Definition 2.4.1-extra-1 (3). Source-facing blocker/check-only entry for the
Sobolev `H¹` penalty clause `(2.47)`.

The source introduces the penalty

`f ↦ (1 / 2) * ∫_Ω ∑ i, (∂f/∂x_i)^2`.

The current repository snapshot still lacks the authoritative domain-local
`H¹(Ω)` owner from Chapter 2. The `#check` commands below record the verified
unit-square smooth-penalty owner from Chapter 8 together with the existing
domain-local `W¹,¹(Ω)` analogue, without replacing the source `H¹(Ω)` owner by
that weaker surrogate.
-/
#check unitSquareSmoothPenalty
#check W11

/- Definition 2.4.1-extra-1 (4). Source-facing blocker/check-only entry for the
homogeneous-Neumann rewriting clause `(2.48)`.

Under homogeneous Neumann boundary conditions, the source rewrites the `H¹`
penalty as
`(1 / 2) * ⟪L f, f⟫_{L²(Ω)}`. The exact Chapter 2 `H¹(Ω)` owner and
negative-Laplacian realization remain unresolved, but the repository does
expose:

* the Chapter 8 homogeneous-Neumann boundary predicate on the unit square,
* a verified unit-square theorem identifying the line derivative of the smooth
  penalty with an `L²` pairing against a diffusion operator under that boundary
  condition, and
* the Chapter 2 smooth negative-Laplacian backend `smoothNegativeLaplacianWithin`
  for the constant-coefficient case.
-/
#check hasVanishingNormalDerivativeOnUnitSquareBoundary
#check lineDeriv_unitSquareSmoothPenalty_eq_unitSquareL2Pairing_of_neumann
#check smoothNegativeLaplacianWithin

/- Definition 2.4.1-extra-1 (5). Source-facing blocker/check-only entry for the
diffusion-type penalty-operator clause `(2.49)`.

The source then names the more general diffusion penalty operator

`L f = -∑ i, ∂/∂x_i (κ * ∂f/∂x_i)`.

The exact Chapter 2 owner for the coefficient `κ`, its ambient domain `Ω`, and
the intended codomain is still unresolved. The repository nevertheless already
contains a verified weighted-diffusion operator surface on the unit square,
which records the same diffusion-type shape without pretending to solve the
missing general-domain ownership question here.
-/
#check unitSquareWeightedDiffusion
#check unitSquareWeightedDiffusion_apply

/- Definition 2.4.1-extra-1 (6). Source-facing blocker/check-only entry for the
negative-entropy clause `(2.50)`.

The source introduces the negative-entropy penalty `f ↦ ⟪f, log f⟫` on an
admissible set `𝒞` from Example 2.27 or Example 2.28.

The exact Chapter 2 owner for that admissible domain and its positivity/log API
is still unresolved. The checks below therefore record:

* the verified Example 2.27 and Example 2.28 admissible-set owners, and
* a backend finite-dimensional log-pairing formula `u ↦ ∑ j, u j * Real.log (u j)`
  that matches the source entropy shape without claiming to be the final owner.
-/
#check EuclideanQuadrant.isClosed_nonnegativeOrthant
#check RealL2.aeNonneg_isClosed

section

variable (n : ℕ)

#check (fun (u : Fin n → ℝ) ↦ ∑ j, u j * Real.log (u j))

end
