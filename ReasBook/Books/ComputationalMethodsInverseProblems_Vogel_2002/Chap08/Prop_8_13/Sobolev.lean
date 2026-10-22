/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9.Pairing

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- The source-facing Sobolev space `W¹,¹(Ω)`, realized as the canonical
submodule of `L¹(Ω) × L¹(Ω; ℝ^d)` cut out by the Chapter 8 weak-gradient
integration-by-parts relation against admissible test fields. -/
@[expose] def w11Submodule
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
    Submodule ℝ
      (MeasureTheory.Lp ℝ 1 (domainMeasure Ω) ×
        MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)) where
  carrier := { f |
    ∀ v : AdmissibleTestField Ω,
      admissibleDivergencePairing f.1 v =
        -∫ x, inner ℝ (f.2 x) (v.toTestFunction x) ∂domainMeasure Ω }
  zero_mem' := by
    sorry
  add_mem' := by
    sorry
  smul_mem' := by
    sorry

/-- A source-facing element of the domain-local Sobolev space `W¹,¹(Ω)`: a
pair `(f, g)` in the canonical Sobolev submodule whose first component is the
underlying `L¹(Ω)` function and whose second component is its weak gradient. -/
abbrev W11 (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) : Type _ :=
  { f :
      MeasureTheory.Lp ℝ 1 (domainMeasure Ω) ×
        MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω) //
      f ∈ w11Submodule Ω }

/-- The source-facing Sobolev notation `W¹,¹(Ω)` for domain-local weakly
once-differentiable `L¹(Ω)` functions. -/
notation "W¹,¹(" Ω ")" => W11 Ω

namespace W11

/-- The canonical `L¹(Ω)` realization of a `W¹,¹(Ω)` element. -/
@[expose] def toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  f.1.1

/-- The weak gradient of a `W¹,¹(Ω)` element. -/
@[expose] def weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) :
    MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω) :=
  f.1.2

/-- Build an element of `W¹,¹(Ω)` from its `L¹(Ω)` realization, weak gradient,
and the defining integration-by-parts law. -/
@[expose]
def ofLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (weakGradient : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω))
    (hPairing :
      ∀ v : AdmissibleTestField Ω,
        admissibleDivergencePairing toL1 v =
          -∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω) :
    W11 Ω :=
  ⟨(toL1, weakGradient), hPairing⟩

/-- `ofLp` recovers the supplied `L¹(Ω)` function. -/
theorem ofLp_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (weakGradient : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω))
    (hPairing :
      ∀ v : AdmissibleTestField Ω,
        admissibleDivergencePairing toL1 v =
          -∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω) :
    (ofLp toL1 weakGradient hPairing).toL1 = toL1 := by
  rfl

/-- `ofLp` recovers the supplied weak gradient. -/
theorem ofLp_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (toL1 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (weakGradient : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω))
    (hPairing :
      ∀ v : AdmissibleTestField Ω,
        admissibleDivergencePairing toL1 v =
          -∫ x, inner ℝ (weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω) :
    (ofLp toL1 weakGradient hPairing).weakGradient = weakGradient := by
  rfl

/-- The defining weak-gradient integration-by-parts law for a `W¹,¹(Ω)`
element. -/
theorem pairing_eq_neg_integral_inner
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) (v : AdmissibleTestField Ω) :
    admissibleDivergencePairing f.toL1 v =
      -∫ x, inner ℝ (f.weakGradient x) (v.toTestFunction x) ∂domainMeasure Ω :=
  f.2 v

/-- Two `W¹,¹(Ω)` elements are equal once their `L¹(Ω)` realizations and weak gradients agree. -/
@[ext] theorem ext
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    {f g : W11 Ω}
    (htoL1 : f.toL1 = g.toL1)
    (hweakGradient : f.weakGradient = g.weakGradient) :
    f = g := by
  exact Subtype.ext (Prod.ext htoL1 hweakGradient)

@[simp] theorem zero_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    ((0 : W11 Ω).toL1) = 0 := rfl

@[simp] theorem zero_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    ((0 : W11 Ω).weakGradient) = 0 := rfl

@[simp] theorem add_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f g : W11 Ω) :
    (f + g).toL1 = f.toL1 + g.toL1 := rfl

@[simp] theorem add_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f g : W11 Ω) :
    (f + g).weakGradient = f.weakGradient + g.weakGradient := rfl

@[simp] theorem neg_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) :
    (-f).toL1 = -f.toL1 := rfl

@[simp] theorem neg_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) :
    (-f).weakGradient = -f.weakGradient := rfl

@[simp] theorem smul_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (a : ℝ) (f : W11 Ω) :
    (a • f).toL1 = a • f.toL1 := rfl

@[simp] theorem smul_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (a : ℝ) (f : W11 Ω) :
    (a • f).weakGradient = a • f.weakGradient := rfl

@[simp] theorem sub_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f g : W11 Ω) :
    (f - g).toL1 = f.toL1 - g.toL1 := rfl

@[simp] theorem sub_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f g : W11 Ω) :
    (f - g).weakGradient = f.weakGradient - g.weakGradient := rfl

@[simp] theorem nsmul_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (n : ℕ) (f : W11 Ω) :
    (n • f).toL1 = n • f.toL1 := rfl

@[simp] theorem nsmul_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (n : ℕ) (f : W11 Ω) :
    (n • f).weakGradient = n • f.weakGradient := rfl

@[simp] theorem zsmul_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (n : ℤ) (f : W11 Ω) :
    (n • f).toL1 = n • f.toL1 := rfl

@[simp] theorem zsmul_weakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (n : ℤ) (f : W11 Ω) :
    (n • f).weakGradient = n • f.weakGradient := rfl

/-- The integral of the norm of the weak gradient of a `W¹,¹(Ω)` element. -/
@[expose]
def integralNormWeakGradient
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) : ℝ :=
  ∫ x, ‖f.weakGradient x‖ ∂domainMeasure Ω

/-- The defining integral formula for `integralNormWeakGradient`. -/
theorem integralNormWeakGradient_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : W11 Ω) :
    f.integralNormWeakGradient = ∫ x, ‖f.weakGradient x‖ ∂domainMeasure Ω := rfl

end W11

end VariationalRegularization
