/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.Calculus.TangentCone.Prod
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.DivergenceTheorem
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2.Diffusion
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2.Penalty
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Exercise_8_2.Pairing

public section

noncomputable section

namespace VariationalRegularization

open MeasureTheory

/-- Helper for Exercise 8.2: the unit square is the standard closed rectangle
`[0,1] × [0,1]`. -/
lemma unitSquare_eq_prod :
    unitSquare = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
  ext p
  exact mem_unitSquare p

/-- Helper for Exercise 8.2: the unit square `[0,1] × [0,1]` has unique
derivatives everywhere, so within-derivatives on it are well behaved. -/
lemma unitSquare_uniqueDiffOn : UniqueDiffOn ℝ unitSquare := by
  -- Rewrite the unit square as the canonical rectangle `Icc (0,0) (1,1)`.
  have hunit :
      unitSquare = Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1 := by
    exact unitSquare_eq_prod
  rw [hunit]
  exact uniqueDiffOn_Icc_zero_one.prod uniqueDiffOn_Icc_zero_one

/-- Helper for Exercise 8.2: the first unit-square partial is affine along the
line `f + τ • h`. -/
lemma unitSquarePartialX_add_smul
    (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    unitSquarePartialX (f + τ • h) p = unitSquarePartialX f p + τ * unitSquarePartialX h p := by
  have hUnique : UniqueDiffWithinAt ℝ unitSquare p := unitSquare_uniqueDiffOn p hp
  have hfdiff : DifferentiableWithinAt ℝ f unitSquare p :=
    (hf.differentiableOn (by simp)) p hp
  have hhdiff : DifferentiableWithinAt ℝ h unitSquare p :=
    (hh.differentiableOn (by simp)) p hp
  -- Rewrite the within-derivative of the line `f + τ • h` using linearity.
  simp only [unitSquarePartialX]
  rw [fderivWithin_add hUnique hfdiff (hhdiff.const_smul τ)]
  rw [fderivWithin_const_smul_field τ hUnique]
  simp

/-- Helper for Exercise 8.2: the second unit-square partial is affine along the
line `f + τ • h`. -/
lemma unitSquarePartialY_add_smul
    (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    unitSquarePartialY (f + τ • h) p = unitSquarePartialY f p + τ * unitSquarePartialY h p := by
  have hUnique : UniqueDiffWithinAt ℝ unitSquare p := unitSquare_uniqueDiffOn p hp
  have hfdiff : DifferentiableWithinAt ℝ f unitSquare p :=
    (hf.differentiableOn (by simp)) p hp
  have hhdiff : DifferentiableWithinAt ℝ h unitSquare p :=
    (hh.differentiableOn (by simp)) p hp
  -- Rewrite the within-derivative of the line `f + τ • h` using linearity.
  simp only [unitSquarePartialY]
  rw [fderivWithin_add hUnique hfdiff (hhdiff.const_smul τ)]
  rw [fderivWithin_const_smul_field τ hUnique]
  simp

/-- Helper for Exercise 8.2: `|∇(f + τ h)|²` expands into the expected quadratic
polynomial in `τ`. -/
lemma unitSquareGradientSq_add_smul
    (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    unitSquareGradientSq (f + τ • h) p =
      unitSquareGradientSq f p + 2 * τ * unitSquareGradientDot f h p +
        τ ^ 2 * unitSquareGradientSq h p := by
  -- Expand the named gradient pieces and collect coefficients in `τ`.
  rw [unitSquareGradientSq, unitSquareGradientSq, unitSquareGradientDot, unitSquareGradientSq]
  rw [unitSquarePartialX_add_smul f h τ p hf hh hp, unitSquarePartialY_add_smul f h τ p hf hh hp]
  ring

/-- Helper for Exercise 8.2: `∇(f + τ h)ᵀ ∇h` is affine in `τ`. -/
lemma unitSquareGradientDot_add_smul_left
    (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    unitSquareGradientDot (f + τ • h) h p =
      unitSquareGradientDot f h p + τ * unitSquareGradientSq h p := by
  -- Expand the named gradient pieces and keep only the first-factor linear terms.
  rw [unitSquareGradientDot, unitSquareGradientDot, unitSquareGradientSq]
  rw [unitSquarePartialX_add_smul f h τ p hf hh hp, unitSquarePartialY_add_smul f h τ p hf hh hp]
  ring

/-- Helper for Exercise 8.2: along the line `f + τ • h`, the squared-gradient
integrand has the expected scalar derivative. -/
lemma hasDerivAt_unitSquareGradientSq_add_smul
    (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    HasDerivAt (fun s : ℝ ↦ unitSquareGradientSq (f + s • h) p)
      (2 * unitSquareGradientDot (f + τ • h) h p) τ := by
  -- Rewrite the squared-gradient integrand as a scalar quadratic in `s`.
  have hpoly :
      (fun s : ℝ ↦ unitSquareGradientSq (f + s • h) p) =
        fun s : ℝ ↦
          unitSquareGradientSq f p + (2 * unitSquareGradientDot f h p) * s +
            unitSquareGradientSq h p * s ^ 2 := by
    funext s
    rw [unitSquareGradientSq_add_smul f h s p hf hh hp]
    ring
  rw [hpoly]
  -- Differentiate the polynomial term-by-term and normalize the answer.
  have hconst : HasDerivAt (fun s : ℝ ↦ unitSquareGradientSq f p) 0 τ :=
    hasDerivAt_const τ (unitSquareGradientSq f p)
  have hlinear :
      HasDerivAt (fun s : ℝ ↦ (2 * unitSquareGradientDot f h p) * s)
        (2 * unitSquareGradientDot f h p) τ := by
    simpa using (hasDerivAt_id τ).const_mul (2 * unitSquareGradientDot f h p)
  have hquadratic :
      HasDerivAt (fun s : ℝ ↦ unitSquareGradientSq h p * s ^ 2)
        (unitSquareGradientSq h p * (2 * τ)) τ := by
    have hsquare : HasDerivAt (fun s : ℝ ↦ s ^ 2) (2 * τ) τ := by
      simpa [two_mul] using hasDerivAt_pow 2 τ
    simpa [pow_two, two_mul] using hsquare.const_mul (unitSquareGradientSq h p)
  have hlinquad :
      HasDerivAt
        (fun s : ℝ ↦ (2 * unitSquareGradientDot f h p) * s + unitSquareGradientSq h p * s ^ 2)
        (2 * unitSquareGradientDot f h p + unitSquareGradientSq h p * (2 * τ)) τ :=
    hlinear.add hquadratic
  have hsum :
      HasDerivAt
        (fun s : ℝ ↦
          unitSquareGradientSq f p +
            ((2 * unitSquareGradientDot f h p) * s + unitSquareGradientSq h p * s ^ 2))
        (2 * unitSquareGradientDot f h p + unitSquareGradientSq h p * (2 * τ)) τ :=
    hlinquad.const_add (unitSquareGradientSq f p)
  simpa [unitSquareGradientDot_add_smul_left f h τ p hf hh hp, two_mul, mul_add, add_assoc,
    mul_assoc, mul_left_comm, mul_comm] using hsum

/-- Helper for Exercise 8.2: the pointwise penalty integrand along the line
`f + τ • h` differentiates by the chain rule. -/
lemma pointwisePenaltyIntegrand_hasDerivAt
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ) (τ : ℝ) (p : ℝ × ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (hp : p ∈ unitSquare) :
    HasDerivAt (fun s : ℝ ↦ ψ (unitSquareGradientSq (f + s • h) p))
      (2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
        unitSquareGradientDot (f + τ • h) h p) τ := by
  -- Apply the one-variable chain rule to the normalized scalar derivative.
  have hψ' :
      HasDerivAt ψ (deriv ψ (unitSquareGradientSq (f + τ • h) p))
        (unitSquareGradientSq (f + τ • h) p) :=
    (hψ.contDiffAt.differentiableAt (by simp)).hasDerivAt
  change
    HasDerivAt (ψ ∘ fun s : ℝ ↦ unitSquareGradientSq (f + s • h) p)
      (2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
        unitSquareGradientDot (f + τ • h) h p) τ
  simpa [Function.comp, mul_assoc, mul_left_comm, mul_comm] using
    hψ'.comp τ (hasDerivAt_unitSquareGradientSq_add_smul f h τ p hf hh hp)

/-- Helper for Exercise 8.2: the first named unit-square partial remains smooth
on `unitSquare` when the original function is smooth there. -/
lemma unitSquarePartialX_contDiffOn
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ ⊤ f unitSquare) :
    ContDiffOn ℝ ⊤ (unitSquarePartialX f) unitSquare := by
  -- View the partial derivative as evaluation of the bundled within-derivative on
  -- the fixed first-coordinate direction.
  have hpair : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ ↦ (p, ((1 : ℝ), (0 : ℝ)))) unitSquare := by
    fun_prop
  convert
    (contDiffOn_fderivWithin_apply (f := f) (s := unitSquare) (m := ⊤) hf unitSquare_uniqueDiffOn
      (by simp)).comp hpair (by intro p hp; exact ⟨hp, Set.mem_univ _⟩) using 1
  ext p
  rfl

/-- Helper for Exercise 8.2: the second named unit-square partial remains smooth
on `unitSquare` when the original function is smooth there. -/
lemma unitSquarePartialY_contDiffOn
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ ⊤ f unitSquare) :
    ContDiffOn ℝ ⊤ (unitSquarePartialY f) unitSquare := by
  -- Evaluate the bundled within-derivative on the fixed second-coordinate direction.
  have hpair : ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ ↦ (p, ((0 : ℝ), (1 : ℝ)))) unitSquare := by
    fun_prop
  convert
    (contDiffOn_fderivWithin_apply (f := f) (s := unitSquare) (m := ⊤) hf unitSquare_uniqueDiffOn
      (by simp)).comp hpair (by intro p hp; exact ⟨hp, Set.mem_univ _⟩) using 1
  ext p
  rfl

/-- Helper for Exercise 8.2: the squared-gradient density is smooth on the unit
square whenever `f` is. -/
lemma unitSquareGradientSq_contDiffOn
    (f : ℝ × ℝ → ℝ) (hf : ContDiffOn ℝ ⊤ f unitSquare) :
    ContDiffOn ℝ ⊤ (unitSquareGradientSq f) unitSquare := by
  -- Expand the definition and combine the smooth named partials.
  change ContDiffOn ℝ ⊤
    (fun p ↦ unitSquarePartialX f p ^ 2 + unitSquarePartialY f p ^ 2) unitSquare
  exact ContDiffOn.add (ContDiffOn.pow (unitSquarePartialX_contDiffOn f hf) 2)
    (ContDiffOn.pow (unitSquarePartialY_contDiffOn f hf) 2)

/-- Helper for Exercise 8.2: the pointwise gradient pairing is smooth on the
unit square when both inputs are. -/
lemma unitSquareGradientDot_contDiffOn
    (f h : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare) :
    ContDiffOn ℝ ⊤ (unitSquareGradientDot f h) unitSquare := by
  -- Expand the pairing into products of the named partial derivatives.
  change ContDiffOn ℝ ⊤
    (fun p ↦
      unitSquarePartialX f p * unitSquarePartialX h p +
        unitSquarePartialY f p * unitSquarePartialY h p) unitSquare
  exact ContDiffOn.add
    (ContDiffOn.mul (unitSquarePartialX_contDiffOn f hf) (unitSquarePartialX_contDiffOn h hh))
    (ContDiffOn.mul (unitSquarePartialY_contDiffOn f hf) (unitSquarePartialY_contDiffOn h hh))

/-- Helper for Exercise 8.2: the weighted `x`-flux attached to `f` is smooth on
the unit square. -/
lemma unitSquarePenaltyFluxX_contDiffOn
    (ψ : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare) :
    ContDiffOn ℝ ⊤
      (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX f q) unitSquare := by
  -- Compose the smooth scalar weight `deriv ψ` with `|∇f|²`, then multiply by `∂ₓf`.
  have hderiv : ContDiff ℝ ⊤ (deriv ψ) := hψ.deriv'
  change ContDiffOn ℝ ⊤ ((deriv ψ ∘ unitSquareGradientSq f) * unitSquarePartialX f) unitSquare
  exact ContDiffOn.mul
    (ContDiffOn.comp (t := Set.univ) hderiv.contDiffOn (unitSquareGradientSq_contDiffOn f hf)
      (by intro x hx; trivial))
    (unitSquarePartialX_contDiffOn f hf)

/-- Helper for Exercise 8.2: the weighted `y`-flux attached to `f` is smooth on
the unit square. -/
lemma unitSquarePenaltyFluxY_contDiffOn
    (ψ : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare) :
    ContDiffOn ℝ ⊤
      (fun q ↦ deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY f q) unitSquare := by
  -- The `y`-flux is the symmetric companion of the `x`-flux.
  have hderiv : ContDiff ℝ ⊤ (deriv ψ) := hψ.deriv'
  change ContDiffOn ℝ ⊤ ((deriv ψ ∘ unitSquareGradientSq f) * unitSquarePartialY f) unitSquare
  exact ContDiffOn.mul
    (ContDiffOn.comp (t := Set.univ) hderiv.contDiffOn (unitSquareGradientSq_contDiffOn f hf)
      (by intro x hx; trivial))
    (unitSquarePartialY_contDiffOn f hf)

/-- Helper for Exercise 8.2: restricting a Fréchet derivative on `unitSquare`
to the horizontal slice `x' ↦ (x', y)` produces the expected one-variable
within-derivative. -/
lemma hasDerivWithinAt_xSlice
    {g : ℝ × ℝ → ℝ} {g' : (ℝ × ℝ) →L[ℝ] ℝ} {x y : ℝ}
    (hg : HasFDerivWithinAt g g' unitSquare (x, y))
    (_hx : x ∈ Set.Icc (0 : ℝ) 1)
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun x' : ℝ ↦ g (x', y)) (g' (1, 0)) (Set.Icc (0 : ℝ) 1) x := by
  -- Compose the two-variable derivative with the affine horizontal embedding.
  have hpair : HasDerivWithinAt (fun x' : ℝ ↦ (x', y)) (1, 0) (Set.Icc (0 : ℝ) 1) x :=
    .prodMk (hasDerivWithinAt_id x (Set.Icc (0 : ℝ) 1))
      (hasDerivWithinAt_const x (Set.Icc (0 : ℝ) 1) y)
  change HasDerivWithinAt (g ∘ fun x' : ℝ ↦ (x', y)) (g' (1, 0)) (Set.Icc (0 : ℝ) 1) x
  exact hg.comp_hasDerivWithinAt x hpair (by
    intro t ht
    exact (mem_unitSquare (t, y)).2 ⟨ht, hy⟩)

/-- Helper for Exercise 8.2: restricting a Fréchet derivative on `unitSquare`
to the vertical slice `y' ↦ (x, y')` produces the expected one-variable
within-derivative. -/
lemma hasDerivWithinAt_ySlice
    {g : ℝ × ℝ → ℝ} {g' : (ℝ × ℝ) →L[ℝ] ℝ} {x y : ℝ}
    (hg : HasFDerivWithinAt g g' unitSquare (x, y))
    (hx : x ∈ Set.Icc (0 : ℝ) 1)
    (_hy : y ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun y' : ℝ ↦ g (x, y')) (g' (0, 1)) (Set.Icc (0 : ℝ) 1) y := by
  -- Compose the two-variable derivative with the affine vertical embedding.
  have hpair : HasDerivWithinAt (fun y' : ℝ ↦ (x, y')) (0, 1) (Set.Icc (0 : ℝ) 1) y :=
    .prodMk (hasDerivWithinAt_const y (Set.Icc (0 : ℝ) 1) x)
      (hasDerivWithinAt_id y (Set.Icc (0 : ℝ) 1))
  change HasDerivWithinAt (g ∘ fun y' : ℝ ↦ (x, y')) (g' (0, 1)) (Set.Icc (0 : ℝ) 1) y
  exact hg.comp_hasDerivWithinAt y hpair (by
    intro t ht
    exact (mem_unitSquare (x, t)).2 ⟨hx, ht⟩)

/-- Helper for Exercise 8.2: the pointwise derivative of the penalty integrand
stays uniformly bounded on the compact strip `[-1,1] × unitSquare`. -/
lemma penaltyLineDerivativeBoundOnStrip
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ τ ∈ Set.Icc (-1 : ℝ) 1, ∀ p ∈ unitSquare,
        ‖2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
            unitSquareGradientDot (f + τ • h) h p‖ ≤ C := by
  let K : Set (ℝ × (ℝ × ℝ)) := Set.Icc (-1 : ℝ) 1 ×ˢ unitSquare
  let g : ℝ × (ℝ × ℝ) → ℝ := fun q ↦
    2 *
      deriv ψ
        (unitSquareGradientSq f q.2 + 2 * q.1 * unitSquareGradientDot f h q.2 +
          q.1 ^ 2 * unitSquareGradientSq h q.2) *
      (unitSquareGradientDot f h q.2 + q.1 * unitSquareGradientSq h q.2)
  have hK : IsCompact K := by
    -- The strip and the closed unit square are compact, so the joint parameter domain is compact.
    dsimp [K]
    rw [unitSquare_eq_prod]
    exact isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hgradSqF :
      ContinuousOn (unitSquareGradientSq f) unitSquare :=
    (unitSquareGradientSq_contDiffOn f hf).continuousOn
  have hgradDot :
      ContinuousOn (unitSquareGradientDot f h) unitSquare :=
    (unitSquareGradientDot_contDiffOn f h hf hh).continuousOn
  have hgradSqH :
      ContinuousOn (unitSquareGradientSq h) unitSquare :=
    (unitSquareGradientSq_contDiffOn h hh).continuousOn
  have hsqOn :
      ContinuousOn
        (fun q : ℝ × (ℝ × ℝ) ↦
          unitSquareGradientSq f q.2 + 2 * q.1 * unitSquareGradientDot f h q.2 +
            q.1 ^ 2 * unitSquareGradientSq h q.2) K := by
    -- Rewrite `|∇(f + τ h)|²` into a polynomial in `τ` whose coefficients are continuous in `p`.
    have hfst : ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ q.1) K := continuous_fst.continuousOn
    have hsndSq :
        ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ unitSquareGradientSq f q.2) K :=
      hgradSqF.comp continuous_snd.continuousOn (by intro q hq; exact hq.2)
    have hsndDot :
        ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ unitSquareGradientDot f h q.2) K :=
      hgradDot.comp continuous_snd.continuousOn (by intro q hq; exact hq.2)
    have hsndSqH :
        ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ unitSquareGradientSq h q.2) K :=
      hgradSqH.comp continuous_snd.continuousOn (by intro q hq; exact hq.2)
    have htmp :
        ContinuousOn
          (fun q : ℝ × (ℝ × ℝ) ↦
            unitSquareGradientSq f q.2 +
              (2 * (q.1 * unitSquareGradientDot f h q.2) +
                q.1 ^ 2 * unitSquareGradientSq h q.2)) K :=
      hsndSq.add <|
        ((ContinuousOn.mul hfst hsndDot).const_mul 2).add <|
          ContinuousOn.mul (ContinuousOn.pow hfst 2) hsndSqH
    simpa [mul_assoc, add_assoc, add_left_comm, add_comm] using htmp
  have hdotOn :
      ContinuousOn
        (fun q : ℝ × (ℝ × ℝ) ↦
          unitSquareGradientDot f h q.2 + q.1 * unitSquareGradientSq h q.2) K := by
    -- The directional gradient pairing is affine in the line parameter `τ`.
    have hfst : ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ q.1) K := continuous_fst.continuousOn
    have hsndDot :
        ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ unitSquareGradientDot f h q.2) K :=
      hgradDot.comp continuous_snd.continuousOn (by intro q hq; exact hq.2)
    have hsndSqH :
        ContinuousOn (fun q : ℝ × (ℝ × ℝ) ↦ unitSquareGradientSq h q.2) K :=
      hgradSqH.comp continuous_snd.continuousOn (by intro q hq; exact hq.2)
    exact hsndDot.add (ContinuousOn.mul hfst hsndSqH)
  have hg :
      ContinuousOn g K := by
    -- Compose the polynomial normalization with the continuous weight `deriv ψ`.
    have hderiv : Continuous (deriv ψ) := hψ.continuous_deriv (by simp)
    exact ContinuousOn.mul
      ((hderiv.comp_continuousOn hsqOn).const_mul 2)
      hdotOn
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn (f := g) hg
  have hC_nonneg : 0 ≤ C := by
    -- The norm bound at `(0,(0,0))` forces the global bound to be nonnegative.
    have hzero_mem : ((0 : ℝ), ((0 : ℝ), (0 : ℝ))) ∈ K := by
      simp [K, unitSquare_eq_prod]
    exact le_trans (norm_nonneg _) (hC _ hzero_mem)
  refine ⟨C, hC_nonneg, ?_⟩
  intro τ hτ p hp
  have hsq :=
    unitSquareGradientSq_add_smul f h τ p hf hh hp
  have hdot :=
    unitSquareGradientDot_add_smul_left f h τ p hf hh hp
  -- Reduce the original derivative integrand to the normalized compact-strip function `g`.
  calc
    ‖2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
        unitSquareGradientDot (f + τ • h) h p‖
      = ‖g (τ, p)‖ := by
          simp [g, hsq, hdot]
    _ ≤ C := hC _ ⟨hτ, hp⟩

/-- Helper for Exercise 8.2: a continuous unit-square integrand is integrable
against the restricted product measure on `(0,1] × (0,1]`. -/
lemma restrictProdIntegrableOfContinuousOn
    (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G unitSquare) :
    Integrable G
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))) := by
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1
  have hs_meas : MeasurableSet (s ×ˢ s) := measurableSet_Ioc.prod measurableSet_Ioc
  have hs_subset : s ×ˢ s ⊆ unitSquare := by
    -- Points in `(0,1] × (0,1]` lie inside the closed unit square.
    intro p hp
    rcases hp with ⟨hx, hy⟩
    exact (mem_unitSquare p).2 ⟨⟨le_of_lt hx.1, hx.2⟩, ⟨le_of_lt hy.1, hy.2⟩⟩
  have h_int : IntegrableOn G (s ×ˢ s) (volume.prod volume) := by
    -- Restrict the continuous integrand from the compact unit square to the measurable sub-rectangle.
    refine hG.integrableOn_of_subset_isCompact ?_ hs_meas hs_subset ?_
    · rw [unitSquare_eq_prod]
      exact isCompact_Icc.prod isCompact_Icc
    · simp [s]
  simpa [IntegrableOn, s, MeasureTheory.Measure.prod_restrict] using h_int

/-- Helper for Exercise 8.2: a continuous unit-square integrand is almost
everywhere strongly measurable for the restricted product measure on
`(0,1] × (0,1]`. -/
lemma restrictProdAEStronglyMeasurableOfContinuousOn
    (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G unitSquare) :
    AEStronglyMeasurable G
      (((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))) := by
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1
  have hs_meas : MeasurableSet (s ×ˢ s) := measurableSet_Ioc.prod measurableSet_Ioc
  have hs_subset : s ×ˢ s ⊆ unitSquare := by
    -- The restricted measure only sees points from the unit square.
    intro p hp
    rcases hp with ⟨hx, hy⟩
    exact (mem_unitSquare p).2 ⟨⟨le_of_lt hx.1, hx.2⟩, ⟨le_of_lt hy.1, hy.2⟩⟩
  have h_meas : AEStronglyMeasurable G ((volume.prod volume).restrict (s ×ˢ s)) :=
    hG.aestronglyMeasurable_of_subset_isCompact
      (by
        rw [unitSquare_eq_prod]
        exact isCompact_Icc.prod isCompact_Icc) hs_meas hs_subset
  simpa [s, MeasureTheory.Measure.prod_restrict] using h_meas

/-- Helper for Exercise 8.2: integrating a continuous unit-square density
against the restricted product measure matches the source iterated
`intervalIntegral` formula. -/
lemma restrictProdIntegral_eq_unitSquareIteratedIntegral
    (G : ℝ × ℝ → ℝ)
    (hG : ContinuousOn G unitSquare) :
    ∫ p, G p ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, G (x, y) := by
  let s : Set ℝ := Set.Ioc (0 : ℝ) 1
  have hs_meas : MeasurableSet (s ×ˢ s) := measurableSet_Ioc.prod measurableSet_Ioc
  have hs_subset : s ×ˢ s ⊆ unitSquare := by
    -- The open-closed rectangle sits inside the closed unit square.
    intro p hp
    rcases hp with ⟨hx, hy⟩
    exact (mem_unitSquare p).2 ⟨⟨le_of_lt hx.1, hx.2⟩, ⟨le_of_lt hy.1, hy.2⟩⟩
  have h_int : IntegrableOn G (s ×ˢ s) (volume.prod volume) := by
    -- Fubini applies because continuity on the compact square gives integrability on the sub-rectangle.
    refine hG.integrableOn_of_subset_isCompact ?_ hs_meas hs_subset ?_
    · rw [unitSquare_eq_prod]
      exact isCompact_Icc.prod isCompact_Icc
    · simp [s]
  calc
    ∫ p, G p ∂((volume.restrict s).prod (volume.restrict s))
        = ∫ p in s ×ˢ s, G p ∂(volume.prod volume) := by
            rw [← MeasureTheory.Measure.prod_restrict]
    _ = ∫ x in s, ∫ y in s, G (x, y) := by
          exact MeasureTheory.setIntegral_prod G h_int
    _ = ∫ x in (0 : ℝ)..1, ∫ y in s, G (x, y) := by
          rw [← intervalIntegral.integral_of_le zero_le_one]
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, G (x, y) := by
          -- Rewrite the inner set integral once more into the source interval-integral spelling.
          congr 1
          ext x
          rw [← intervalIntegral.integral_of_le zero_le_one]

/-- Helper for Exercise 8.2: the outer `1 / 2` from `J` cancels the chain-rule
factor `2` inside the differentiated iterated integral. -/
lemma half_two_unitSquareIteratedIntegral
    (G : ℝ × ℝ → ℝ) :
    (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, 2 * G (x, y)) =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, G (x, y) := by
  have hinner :
      (fun x : ℝ => ∫ y in (0 : ℝ)..1, 2 * G (x, y)) =
        fun x : ℝ => 2 * ∫ y in (0 : ℝ)..1, G (x, y) := by
    -- Pull the scalar `2` out of the inner interval integral first.
    funext x
    rw [intervalIntegral.integral_const_mul]
  rw [hinner]
  -- Then pull the same scalar out of the outer integral and finish by scalar algebra.
  rw [intervalIntegral.integral_const_mul]
  ring

/-- Helper for Exercise 8.2: the weighted penalty fluxes vanish on the
corresponding edges once the normal derivative of `f` vanishes on the unit
square boundary. -/
lemma penaltyFluxBoundaryVanishes
    (ψ : ℝ → ℝ) (f : ℝ × ℝ → ℝ)
    (h_neumann : hasVanishingNormalDerivativeOnUnitSquareBoundary f) :
    (∀ y ∈ Set.Icc (0 : ℝ) 1,
        deriv ψ (unitSquareGradientSq f (0, y)) * unitSquarePartialX f (0, y) = 0 ∧
          deriv ψ (unitSquareGradientSq f (1, y)) * unitSquarePartialX f (1, y) = 0) ∧
      (∀ x ∈ Set.Icc (0 : ℝ) 1,
        deriv ψ (unitSquareGradientSq f (x, 0)) * unitSquarePartialY f (x, 0) = 0 ∧
          deriv ψ (unitSquareGradientSq f (x, 1)) * unitSquarePartialY f (x, 1) = 0) := by
  constructor
  · intro y hy
    constructor
    · have hx0 : unitSquarePartialX f (0, y) = 0 := by
        -- The left edge belongs to the unit-square boundary, so the horizontal flux factor vanishes there.
        exact (h_neumann (0, y) (by
          rw [mem_unitSquareBoundary]
          exact ⟨by simp, hy, Or.inl rfl⟩)).1 (Or.inl rfl)
      rw [hx0]
      ring
    · have hx1 : unitSquarePartialX f (1, y) = 0 := by
        -- The right edge is handled by the same Neumann boundary condition.
        exact (h_neumann (1, y) (by
          rw [mem_unitSquareBoundary]
          exact ⟨by simp, hy, Or.inr <| Or.inl rfl⟩)).1 (Or.inr rfl)
      rw [hx1]
      ring
  · intro x hx
    constructor
    · have hy0 : unitSquarePartialY f (x, 0) = 0 := by
        -- On the lower edge, the vertical normal derivative vanishes.
        exact (h_neumann (x, 0) (by
          rw [mem_unitSquareBoundary]
          exact ⟨hx, by simp, Or.inr <| Or.inr <| Or.inl rfl⟩)).2 (Or.inl rfl)
      rw [hy0]
      ring
    · have hy1 : unitSquarePartialY f (x, 1) = 0 := by
        -- On the upper edge, the same vertical boundary condition applies.
        exact (h_neumann (x, 1) (by
          rw [mem_unitSquareBoundary]
          exact ⟨hx, by simp, Or.inr <| Or.inr <| Or.inr rfl⟩)).2 (Or.inr rfl)
      rw [hy1]
      ring

/-- Helper for Exercise 8.2: differentiating the restricted-product penalty
integral at `τ = 0` gives the product-measure version of the first variation. -/
lemma hasDerivAt_penaltyLineRestrictProdIntegral
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare) :
    HasDerivAt
      (fun τ : ℝ ↦
        ∫ p, ψ (unitSquareGradientSq (f + τ • h) p)
          ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))))
      (∫ p, 2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p
        ∂((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1))))
      0 := by
  let μ : Measure (ℝ × ℝ) :=
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  let strip : Set ℝ := Set.Icc (-1 : ℝ) 1
  have hstrip : strip ∈ nhds (0 : ℝ) := by
    -- Use a fixed compact strip around `0` for the dominated-differentiation theorem.
    refine Icc_mem_nhds ?_ ?_ <;> norm_num
  have hF_meas :
      ∀ᶠ τ in nhds (0 : ℝ),
        AEStronglyMeasurable (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq (f + τ • h) p)) μ := by
    refine Filter.Eventually.of_forall ?_
    intro τ
    have hline : ContDiffOn ℝ ⊤ (f + τ • h) unitSquare :=
      ContDiffOn.add hf (ContDiffOn.const_smul τ hh)
    have hcont :
        ContinuousOn (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq (f + τ • h) p)) unitSquare :=
      (hψ.continuous.continuousOn.comp
        (unitSquareGradientSq_contDiffOn (f + τ • h) hline).continuousOn
        (by intro p hp; exact Set.mem_univ _))
    -- Continuity on the unit square supplies the required measurability on the restricted measure.
    exact restrictProdAEStronglyMeasurableOfContinuousOn _ hcont
  have hF_int :
      Integrable (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq f p)) μ := by
    have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq f p)) unitSquare :=
      (hψ.continuous.continuousOn.comp (unitSquareGradientSq_contDiffOn f hf).continuousOn
        (by intro p hp; exact Set.mem_univ _))
    -- The base integrand is continuous on the compact square, hence integrable on the restricted rectangle.
    simpa [μ] using restrictProdIntegrableOfContinuousOn _ hcont
  have hF'_meas :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ ↦ 2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p) μ := by
    have hweight :
        ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ ↦ deriv ψ (unitSquareGradientSq f p)) unitSquare := by
      exact ContDiffOn.comp (s := unitSquare) (t := Set.univ) hψ.deriv'.contDiffOn
        (unitSquareGradientSq_contDiffOn f hf) (by intro p hp; simp)
    have hcont :
        ContinuousOn
          (fun p : ℝ × ℝ ↦ 2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p)
          unitSquare := by
      have hcont' :=
        (ContDiffOn.mul (ContDiffOn.const_smul 2 hweight) (unitSquareGradientDot_contDiffOn f h hf hh)).continuousOn
      simpa [smul_eq_mul, mul_assoc] using hcont'
    -- The derivative integrand at `τ = 0` is again continuous on the unit square.
    simpa [μ] using restrictProdAEStronglyMeasurableOfContinuousOn _ hcont
  obtain ⟨C, hC_nonneg, hC⟩ := penaltyLineDerivativeBoundOnStrip ψ f h hψ hf hh
  have hbound_int : Integrable (fun _ : ℝ × ℝ ↦ C) μ := by
    have hcont : ContinuousOn (fun _ : ℝ × ℝ ↦ C) unitSquare := by
      intro p hp
      simpa using continuousWithinAt_const
    -- A constant bound is integrable because the restricted rectangle has finite measure.
    simpa [μ] using restrictProdIntegrableOfContinuousOn (fun _ : ℝ × ℝ ↦ C) hcont
  have h_bound :
      ∀ᵐ p ∂μ, ∀ τ ∈ strip,
        ‖2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
            unitSquareGradientDot (f + τ • h) h p‖ ≤ C := by
    have hs_meas : MeasurableSet ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1) :=
      measurableSet_Ioc.prod measurableSet_Ioc
    have h_bound_restrict :
        ∀ᵐ p ∂((volume.prod volume).restrict ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1)),
          ∀ τ ∈ strip,
            ‖2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
                unitSquareGradientDot (f + τ • h) h p‖ ≤ C := by
      rw [ae_restrict_iff' hs_meas]
      refine Filter.Eventually.of_forall ?_
      intro p hp τ hτ
      -- On the restricted support, the compact-strip bound applies directly.
      exact hC τ hτ p <| (mem_unitSquare p).2
        ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
    simpa [μ, MeasureTheory.Measure.prod_restrict] using h_bound_restrict
  have h_diff :
      ∀ᵐ p ∂μ, ∀ τ ∈ strip,
        HasDerivAt (fun s : ℝ ↦ ψ (unitSquareGradientSq (f + s • h) p))
          (2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
            unitSquareGradientDot (f + τ • h) h p) τ := by
    have hs_meas : MeasurableSet ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1) :=
      measurableSet_Ioc.prod measurableSet_Ioc
    have h_diff_restrict :
        ∀ᵐ p ∂((volume.prod volume).restrict ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1)),
          ∀ τ ∈ strip,
            HasDerivAt (fun s : ℝ ↦ ψ (unitSquareGradientSq (f + s • h) p))
              (2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
                unitSquareGradientDot (f + τ • h) h p) τ := by
      rw [ae_restrict_iff' hs_meas]
      refine Filter.Eventually.of_forall ?_
      intro p hp τ hτ
      -- The pointwise chain-rule lemma closes the derivative on every point of the restricted support.
      exact pointwisePenaltyIntegrand_hasDerivAt ψ f h τ p hψ hf hh <|
        (mem_unitSquare p).2 ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
    simpa [μ, MeasureTheory.Measure.prod_restrict] using h_diff_restrict
  have hF_int_zero :
      Integrable (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq (f + (0 : ℝ) • h) p)) μ := by
    simpa using hF_int
  have hF'_meas_zero :
      AEStronglyMeasurable
        (fun p : ℝ × ℝ ↦
          2 * deriv ψ (unitSquareGradientSq (f + (0 : ℝ) • h) p) *
            unitSquareGradientDot (f + (0 : ℝ) • h) h p) μ := by
    simpa using hF'_meas
  simpa [μ, strip] using
    (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      (μ := μ) (s := strip)
      (bound := fun _ : ℝ × ℝ ↦ C)
      (F := fun τ p ↦ ψ (unitSquareGradientSq (f + τ • h) p))
      (F' := fun τ p ↦
        2 * deriv ψ (unitSquareGradientSq (f + τ • h) p) *
          unitSquareGradientDot (f + τ • h) h p)
      hstrip hF_meas hF_int_zero hF'_meas_zero h_bound hbound_int h_diff).2

/-- Exercise 8.2 (1). For the smooth unit-square penalty `(8.28)`, the
directional derivative `δJ(f; h)` is the integral of `ψ'(|∇f|²) ∇fᵀ ∇h` over
`[0,1] × [0,1]`. -/
theorem lineDeriv_unitSquareSmoothPenalty_eq_integral
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare) :
    lineDeriv ℝ (unitSquareSmoothPenalty ψ) f h =
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        deriv ψ (unitSquareGradientSq f (x, y)) * unitSquareGradientDot f h (x, y) := by
  let μ : Measure (ℝ × ℝ) :=
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  have hderivProd :=
    hasDerivAt_penaltyLineRestrictProdIntegral ψ f h hψ hf hh
  have hderiv :
      HasDerivAt
        (fun τ : ℝ ↦ unitSquareSmoothPenalty ψ (f + τ • h))
        ((1 / 2 : ℝ) *
          ∫ p, 2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p ∂μ) 0 := by
    have hformula :
        (fun τ : ℝ ↦ unitSquareSmoothPenalty ψ (f + τ • h)) =
          fun τ : ℝ ↦
            (1 / 2 : ℝ) *
              ∫ p, ψ (unitSquareGradientSq (f + τ • h) p) ∂μ := by
      -- Route correction: keep the line-parameter proof in the restricted-product world and bridge
      -- back to nested interval integrals only after differentiation is done.
      funext τ
      rw [unitSquareSmoothPenalty_def]
      have hline : ContDiffOn ℝ ⊤ (f + τ • h) unitSquare :=
        ContDiffOn.add hf (ContDiffOn.const_smul τ hh)
      have hcont :
          ContinuousOn (fun p : ℝ × ℝ ↦ ψ (unitSquareGradientSq (f + τ • h) p)) unitSquare :=
        (hψ.continuous.continuousOn.comp
          (unitSquareGradientSq_contDiffOn (f + τ • h) hline).continuousOn
          (by intro p hp; exact Set.mem_univ _))
      rw [← restrictProdIntegral_eq_unitSquareIteratedIntegral _ hcont]
    rw [hformula]
    -- Differentiate the product-measure integral, then multiply by the outer factor `1 / 2`.
    simpa [μ] using hderivProd.const_mul (1 / 2 : ℝ)
  have hcont :
      ContinuousOn
        (fun p : ℝ × ℝ ↦ 2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p)
        unitSquare := by
    have hweight :
        ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ ↦ deriv ψ (unitSquareGradientSq f p)) unitSquare := by
      exact ContDiffOn.comp (s := unitSquare) (t := Set.univ) hψ.deriv'.contDiffOn
        (unitSquareGradientSq_contDiffOn f hf) (by intro p hp; exact Set.mem_univ _)
    -- The final bridge uses continuity of the differentiated density on the unit square.
    have hcont' :=
      (ContDiffOn.mul (ContDiffOn.const_smul 2 hweight) (unitSquareGradientDot_contDiffOn f h hf hh)).continuousOn
    simpa [smul_eq_mul, mul_assoc] using hcont'
  have hline :
      HasLineDerivAt ℝ (unitSquareSmoothPenalty ψ)
        ((1 / 2 : ℝ) * ∫ p,
          2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p ∂μ)
        f h := by
    simpa [HasLineDerivAt, μ] using hderiv
  calc
    lineDeriv ℝ (unitSquareSmoothPenalty ψ) f h
      = (1 / 2 : ℝ) * ∫ p,
          2 * deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p ∂μ :=
          hline.lineDeriv
    _ = (1 / 2 : ℝ) *
          (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
            2 * deriv ψ (unitSquareGradientSq f (x, y)) * unitSquareGradientDot f h (x, y)) := by
          rw [restrictProdIntegral_eq_unitSquareIteratedIntegral _ hcont]
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          deriv ψ (unitSquareGradientSq f (x, y)) * unitSquareGradientDot f h (x, y) := by
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            half_two_unitSquareIteratedIntegral
              (fun p : ℝ × ℝ ↦ deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p)

/-- Helper for Exercise 8.2: the within-divergence of the weighted flux product
`(fluxX * h, fluxY * h)` splits into the first-variation density minus the
weighted-diffusion pairing density. -/
lemma weightedFluxProductDivergenceWithin_eq
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (p : ℝ × ℝ) (hp : p ∈ unitSquare) :
    unitSquarePartialX
        (fun q ↦ (deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX f q) * h q) p +
      unitSquarePartialY
        (fun q ↦ (deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY f q) * h q) p =
      deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p -
        unitSquareWeightedDiffusion ψ f f p * h p := by
  let fluxX : ℝ × ℝ → ℝ := fun q ↦
    deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX f q
  let fluxY : ℝ × ℝ → ℝ := fun q ↦
    deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY f q
  have hUnique : UniqueDiffWithinAt ℝ unitSquare p := unitSquare_uniqueDiffOn p hp
  have hfluxXDiff : DifferentiableWithinAt ℝ fluxX unitSquare p := by
    -- The weighted `x`-flux is smooth on `unitSquare`, hence differentiable there.
    simpa [fluxX] using
      (unitSquarePenaltyFluxX_contDiffOn ψ f hψ hf).differentiableOn (by simp) p hp
  have hfluxYDiff : DifferentiableWithinAt ℝ fluxY unitSquare p := by
    -- The `y`-flux is the symmetric smooth companion.
    simpa [fluxY] using
      (unitSquarePenaltyFluxY_contDiffOn ψ f hψ hf).differentiableOn (by simp) p hp
  have hhDiff : DifferentiableWithinAt ℝ h unitSquare p :=
    (hh.differentiableOn (by simp)) p hp
  -- Expand the two product rules once and regroup the `x`- and `y`-contributions.
  simp only [unitSquarePartialX_def, unitSquarePartialY_def]
  change
      fderivWithin ℝ (fluxX * h) unitSquare p (1, 0) +
        fderivWithin ℝ (fluxY * h) unitSquare p (0, 1) =
      deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p -
        unitSquareWeightedDiffusion ψ f f p * h p
  rw [fderivWithin_mul hUnique hfluxXDiff hhDiff, fderivWithin_mul hUnique hfluxYDiff hhDiff]
  -- The named partial-derivative APIs reduce the identity to commutative-ring algebra.
  simp [fluxX, fluxY, unitSquareGradientDot_def, unitSquareWeightedDiffusion_apply,
    unitSquarePartialX_def, unitSquarePartialY_def, smul_eq_mul, mul_left_comm, mul_comm]
  ring

/-- Helper for Exercise 8.2: the divergence-theorem boundary term attached to
the weighted flux products vanishes under the Neumann boundary condition on
`f`. -/
lemma weightedFluxBoundaryTerm_zero
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (h_neumann : hasVanishingNormalDerivativeOnUnitSquareBoundary f) :
    (((∫ x in (0 : ℝ)..1,
          (deriv ψ (unitSquareGradientSq f (x, 1)) * unitSquarePartialY f (x, 1)) * h (x, 1)) -
        ∫ x in (0 : ℝ)..1,
          (deriv ψ (unitSquareGradientSq f (x, 0)) * unitSquarePartialY f (x, 0)) * h (x, 0)) +
        ∫ y in (0 : ℝ)..1,
          (deriv ψ (unitSquareGradientSq f (1, y)) * unitSquarePartialX f (1, y)) * h (1, y)) -
      ∫ y in (0 : ℝ)..1,
        (deriv ψ (unitSquareGradientSq f (0, y)) * unitSquarePartialX f (0, y)) * h (0, y) = 0 := by
  rcases penaltyFluxBoundaryVanishes ψ f h_neumann with ⟨hX, hY⟩
  have hTop :
      ∫ x in (0 : ℝ)..1,
        (deriv ψ (unitSquareGradientSq f (x, 1)) * unitSquarePartialY f (x, 1)) * h (x, 1) = 0 := by
    -- The top-edge integrand vanishes pointwise because the weighted vertical flux is zero there.
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards with x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      have hxIcc : x ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) := ⟨le_of_lt hx.1, hx.2⟩
      simpa using hxIcc
    have hzero :
        deriv ψ (unitSquareGradientSq f (x, 1)) * unitSquarePartialY f (x, 1) = 0 := (hY x hx').2
    simp [hzero]
  have hBottom :
      ∫ x in (0 : ℝ)..1,
        (deriv ψ (unitSquareGradientSq f (x, 0)) * unitSquarePartialY f (x, 0)) * h (x, 0) = 0 := by
    -- The same boundary vanishing holds on the bottom edge.
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards with x hx
    have hx' : x ∈ Set.Icc (0 : ℝ) 1 := by
      have hxIcc : x ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) := ⟨le_of_lt hx.1, hx.2⟩
      simpa using hxIcc
    have hzero :
        deriv ψ (unitSquareGradientSq f (x, 0)) * unitSquarePartialY f (x, 0) = 0 := (hY x hx').1
    simp [hzero]
  have hRight :
      ∫ y in (0 : ℝ)..1,
        (deriv ψ (unitSquareGradientSq f (1, y)) * unitSquarePartialX f (1, y)) * h (1, y) = 0 := by
    -- The right-edge weighted horizontal flux vanishes.
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards with y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
      have hyIcc : y ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) := ⟨le_of_lt hy.1, hy.2⟩
      simpa using hyIcc
    have hzero :
        deriv ψ (unitSquareGradientSq f (1, y)) * unitSquarePartialX f (1, y) = 0 := (hX y hy').2
    simp [hzero]
  have hLeft :
      ∫ y in (0 : ℝ)..1,
        (deriv ψ (unitSquareGradientSq f (0, y)) * unitSquarePartialX f (0, y)) * h (0, y) = 0 := by
    -- The left-edge horizontal flux vanishes as well.
    refine intervalIntegral.integral_zero_ae ?_
    filter_upwards with y hy
    have hy' : y ∈ Set.Icc (0 : ℝ) 1 := by
      have hyIcc : y ∈ Set.Icc (min (0 : ℝ) 1) (max (0 : ℝ) 1) := ⟨le_of_lt hy.1, hy.2⟩
      simpa using hyIcc
    have hzero :
        deriv ψ (unitSquareGradientSq f (0, y)) * unitSquarePartialX f (0, y) = 0 := (hX y hy').1
    simp [hzero]
  -- Substitute the four zero boundary integrals into the rectangle formula.
  simp [hTop, hBottom, hRight, hLeft]

/-- Helper for Exercise 8.2: under the Neumann boundary condition on `f`, the
gradient-pairing integral from part (1) equals the unit-square `L²` pairing
with the weighted diffusion operator. -/
lemma integral_weightedGradient_eq_unitSquareL2Pairing_of_neumann
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (h_neumann : hasVanishingNormalDerivativeOnUnitSquareBoundary f) :
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      deriv ψ (unitSquareGradientSq f (x, y)) * unitSquareGradientDot f h (x, y) =
      unitSquareL2Pairing (unitSquareWeightedDiffusion ψ f f) h := by
  let μ : Measure (ℝ × ℝ) :=
    ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) 1)))
  let fluxX : ℝ × ℝ → ℝ := fun q ↦
    deriv ψ (unitSquareGradientSq f q) * unitSquarePartialX f q
  let fluxY : ℝ × ℝ → ℝ := fun q ↦
    deriv ψ (unitSquareGradientSq f q) * unitSquarePartialY f q
  let Fx : ℝ × ℝ → ℝ := fun q ↦ fluxX q * h q
  let Fy : ℝ × ℝ → ℝ := fun q ↦ fluxY q * h q
  let firstVariationDensity : ℝ × ℝ → ℝ := fun p ↦
    deriv ψ (unitSquareGradientSq f p) * unitSquareGradientDot f h p
  let pairingDensity : ℝ × ℝ → ℝ := fun p ↦
    unitSquareWeightedDiffusion ψ f f p * h p
  let divergenceDensity : ℝ × ℝ → ℝ := fun p ↦ unitSquarePartialX Fx p + unitSquarePartialY Fy p
  let differenceDensity : ℝ × ℝ → ℝ := fun p ↦ firstVariationDensity p - pairingDensity p
  have hFluxX : ContDiffOn ℝ ⊤ fluxX unitSquare := by
    simpa [fluxX] using unitSquarePenaltyFluxX_contDiffOn ψ f hψ hf
  have hFluxY : ContDiffOn ℝ ⊤ fluxY unitSquare := by
    simpa [fluxY] using unitSquarePenaltyFluxY_contDiffOn ψ f hψ hf
  have hFx : ContDiffOn ℝ ⊤ Fx unitSquare := by
    -- Multiply the smooth weighted `x`-flux by the smooth test function `h`.
    simpa [Fx] using ContDiffOn.mul hFluxX hh
  have hFy : ContDiffOn ℝ ⊤ Fy unitSquare := by
    -- The `y`-component is handled symmetrically.
    simpa [Fy] using ContDiffOn.mul hFluxY hh
  have hWeight :
      ContDiffOn ℝ ⊤ (fun p : ℝ × ℝ ↦ deriv ψ (unitSquareGradientSq f p)) unitSquare := by
    exact ContDiffOn.comp (s := unitSquare) (t := Set.univ) hψ.deriv'.contDiffOn
      (unitSquareGradientSq_contDiffOn f hf) (by intro p hp; simp)
  have hFirstVariation : ContinuousOn firstVariationDensity unitSquare := by
    -- The first-variation density is a product of two continuous unit-square factors.
    simpa [firstVariationDensity] using
      (ContDiffOn.mul hWeight (unitSquareGradientDot_contDiffOn f h hf hh)).continuousOn
  have hDiffusion : ContinuousOn (unitSquareWeightedDiffusion ψ f f) unitSquare := by
    have hDx : ContinuousOn (unitSquarePartialX fluxX) unitSquare :=
      (unitSquarePartialX_contDiffOn fluxX hFluxX).continuousOn
    have hDy : ContinuousOn (unitSquarePartialY fluxY) unitSquare :=
      (unitSquarePartialY_contDiffOn fluxY hFluxY).continuousOn
    -- Expand the weighted diffusion operator into the two flux partials.
    show ContinuousOn ((-unitSquarePartialX fluxX) - unitSquarePartialY fluxY) unitSquare
    simpa [fluxX, fluxY, unitSquareWeightedDiffusion_apply] using hDx.neg.sub hDy
  have hPairing : ContinuousOn pairingDensity unitSquare := by
    -- Multiplying the diffusion factor by `h` gives the pairing density.
    change ContinuousOn ((unitSquareWeightedDiffusion ψ f f) * h) unitSquare
    simpa [pairingDensity] using hDiffusion.mul hh.continuousOn
  have hDivergence : ContinuousOn divergenceDensity unitSquare := by
    have hDx : ContinuousOn (unitSquarePartialX Fx) unitSquare :=
      (unitSquarePartialX_contDiffOn Fx hFx).continuousOn
    have hDy : ContinuousOn (unitSquarePartialY Fy) unitSquare :=
      (unitSquarePartialY_contDiffOn Fy hFy).continuousOn
    -- The divergence density is the sum of the two named within-partials.
    change ContinuousOn (unitSquarePartialX Fx + unitSquarePartialY Fy) unitSquare
    simpa [divergenceDensity] using hDx.add hDy
  have hDifference : ContinuousOn differenceDensity unitSquare := by
    -- The pointwise flux identity compares the divergence density with this difference density.
    change ContinuousOn (firstVariationDensity - pairingDensity) unitSquare
    simpa [differenceDensity] using hFirstVariation.sub hPairing
  have hDivergenceInt :
      IntegrableOn divergenceDensity unitSquare := by
    -- Continuity on the compact unit square gives the integrability required by the divergence theorem.
    refine hDivergence.integrableOn_of_subset_isCompact ?_ ?_ subset_rfl ?_
    · rw [unitSquare_eq_prod]
      exact isCompact_Icc.prod isCompact_Icc
    · rw [unitSquare_eq_prod]
      exact measurableSet_Icc.prod measurableSet_Icc
    · rw [unitSquare_eq_prod]
      exact (isCompact_Icc.prod isCompact_Icc).measure_ne_top
  have hDivergenceZero :
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, divergenceDensity (x, y) = 0 := by
    have hRect :=
      MeasureTheory.integral2_divergence_prod_of_hasFDerivAt
        Fx Fy
        (fun p ↦ fderivWithin ℝ Fx unitSquare p)
        (fun p ↦ fderivWithin ℝ Fy unitSquare p)
        (0 : ℝ) (0 : ℝ) 1 1
        (by
          -- The divergence theorem sees the two weighted flux products as continuous on the full rectangle.
          simpa [unitSquare_eq_prod, Set.uIcc_of_le zero_le_one, Fx] using hFx.continuousOn)
        (by
          -- The second flux product is continuous for the same reason.
          simpa [unitSquare_eq_prod, Set.uIcc_of_le zero_le_one, Fy] using hFy.continuousOn)
        (by
          intro p hp
          have hp' : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
            simpa using hp
          have hpSquare : p ∈ unitSquare := by
            exact (mem_unitSquare p).2
              ⟨⟨le_of_lt hp'.1.1, le_of_lt hp'.1.2⟩, ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩⟩
          have hNhds : unitSquare ∈ nhds p := by
            rw [unitSquare_eq_prod]
            exact prod_mem_nhds (Icc_mem_nhds hp'.1.1 hp'.1.2) (Icc_mem_nhds hp'.2.1 hp'.2.2)
          -- Upgrade the within-derivative witness to an ordinary derivative on the interior.
          exact ((hFx.differentiableOn (by simp)) p hpSquare).hasFDerivWithinAt.hasFDerivAt hNhds)
        (by
          intro p hp
          have hp' : p ∈ Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) 1 := by
            simpa using hp
          have hpSquare : p ∈ unitSquare := by
            exact (mem_unitSquare p).2
              ⟨⟨le_of_lt hp'.1.1, le_of_lt hp'.1.2⟩, ⟨le_of_lt hp'.2.1, le_of_lt hp'.2.2⟩⟩
          have hNhds : unitSquare ∈ nhds p := by
            rw [unitSquare_eq_prod]
            exact prod_mem_nhds (Icc_mem_nhds hp'.1.1 hp'.1.2) (Icc_mem_nhds hp'.2.1 hp'.2.2)
          -- The `y`-component uses the same interior upgrade.
          exact ((hFy.differentiableOn (by simp)) p hpSquare).hasFDerivWithinAt.hasFDerivAt hNhds)
        (by
          -- The divergence integrand is continuous on the compact square, hence integrable there.
          simpa [divergenceDensity, unitSquare_eq_prod, Set.uIcc_of_le zero_le_one,
            unitSquarePartialX_def, unitSquarePartialY_def] using hDivergenceInt)
    calc
      ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1, divergenceDensity (x, y)
        = (((∫ x in (0 : ℝ)..1, Fy (x, 1)) - ∫ x in (0 : ℝ)..1, Fy (x, 0)) +
            ∫ y in (0 : ℝ)..1, Fx (1, y)) - ∫ y in (0 : ℝ)..1, Fx (0, y) := by
            simpa [divergenceDensity, unitSquarePartialX_def, unitSquarePartialY_def] using hRect
      _ = 0 := by
            -- The Neumann hypothesis annihilates the whole boundary contribution.
            simpa [Fx, Fy, fluxX, fluxY] using weightedFluxBoundaryTerm_zero ψ f h h_neumann
  have hProdDivergenceZero :
      ∫ p, divergenceDensity p ∂μ = 0 := by
    -- Rewrite the iterated integral from the divergence theorem back into the restricted-product measure.
    rw [restrictProdIntegral_eq_unitSquareIteratedIntegral divergenceDensity hDivergence]
    exact hDivergenceZero
  have hProdEq :
      ∫ p, divergenceDensity p ∂μ = ∫ p, differenceDensity p ∂μ := by
    have hsMeas : MeasurableSet ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1) :=
      measurableSet_Ioc.prod measurableSet_Ioc
    have hEqRestrict :
        ∀ᵐ p ∂((volume.prod volume).restrict ((Set.Ioc (0 : ℝ) 1) ×ˢ Set.Ioc (0 : ℝ) 1)),
          divergenceDensity p = differenceDensity p := by
      rw [ae_restrict_iff' hsMeas]
      refine Filter.Eventually.of_forall ?_
      intro p hp
      have hpSquare : p ∈ unitSquare := by
        exact (mem_unitSquare p).2
          ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩
      -- On the support of the restricted-product measure, the pointwise divergence identity applies.
      simpa [divergenceDensity, differenceDensity, Fx, Fy, fluxX, fluxY, firstVariationDensity,
        pairingDensity] using
        weightedFluxProductDivergenceWithin_eq ψ f h hψ hf hh p hpSquare
    simpa [μ, MeasureTheory.Measure.prod_restrict] using integral_congr_ae hEqRestrict
  have hProdDifferenceZero :
      ∫ p, differenceDensity p ∂μ = 0 := by
    calc
      ∫ p, differenceDensity p ∂μ = ∫ p, divergenceDensity p ∂μ := hProdEq.symm
      _ = 0 := hProdDivergenceZero
  have hFirstInt : Integrable firstVariationDensity μ := by
    simpa [μ] using restrictProdIntegrableOfContinuousOn firstVariationDensity hFirstVariation
  have hPairingInt : Integrable pairingDensity μ := by
    simpa [μ] using restrictProdIntegrableOfContinuousOn pairingDensity hPairing
  have hProdFirstEq :
      ∫ p, firstVariationDensity p ∂μ = ∫ p, pairingDensity p ∂μ := by
    apply sub_eq_zero.mp
    calc
      ∫ p, firstVariationDensity p ∂μ - ∫ p, pairingDensity p ∂μ
        = ∫ p, differenceDensity p ∂μ := by
            symm
            simpa [differenceDensity] using integral_sub hFirstInt hPairingInt
      _ = 0 := hProdDifferenceZero
  calc
    ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
        deriv ψ (unitSquareGradientSq f (x, y)) * unitSquareGradientDot f h (x, y)
      = ∫ p, firstVariationDensity p ∂μ := by
          -- Rewrite the source iterated integral as a restricted-product integral.
          symm
          exact restrictProdIntegral_eq_unitSquareIteratedIntegral firstVariationDensity hFirstVariation
    _ = ∫ p, pairingDensity p ∂μ := hProdFirstEq
    _ = ∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
          unitSquareWeightedDiffusion ψ f f (x, y) * h (x, y) := by
          -- Convert the pairing density back to the textbook iterated-integral spelling.
          simpa [pairingDensity] using
            restrictProdIntegral_eq_unitSquareIteratedIntegral pairingDensity hPairing
    _ = unitSquareL2Pairing (unitSquareWeightedDiffusion ψ f f) h := by
          rw [unitSquareL2Pairing_def]

/-- Exercise 8.2 (2). If the normal derivative of `f` vanishes on the boundary
of the unit square, then the directional derivative of `(8.28)` equals the
unit-square `L²` pairing with the weighted diffusion operator `(8.27)`. -/
theorem lineDeriv_unitSquareSmoothPenalty_eq_unitSquareL2Pairing_of_neumann
    (ψ : ℝ → ℝ) (f h : ℝ × ℝ → ℝ)
    (hψ : ContDiff ℝ ⊤ ψ)
    (hf : ContDiffOn ℝ ⊤ f unitSquare)
    (hh : ContDiffOn ℝ ⊤ h unitSquare)
    (h_neumann : hasVanishingNormalDerivativeOnUnitSquareBoundary f) :
    lineDeriv ℝ (unitSquareSmoothPenalty ψ) f h =
      unitSquareL2Pairing (unitSquareWeightedDiffusion ψ f f) h := by
  -- Route correction: replace the unstable slice-by-slice integration-by-parts
  -- route with one rectangle divergence computation for the weighted flux field.
  rw [lineDeriv_unitSquareSmoothPenalty_eq_integral ψ f h hψ hf hh]
  -- Part (1) reduces the theorem to the integral identity proved by the divergence theorem.
  exact integral_weightedGradient_eq_unitSquareL2Pairing_of_neumann ψ f h hψ hf hh h_neumann

end VariationalRegularization
