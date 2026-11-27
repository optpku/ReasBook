/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9.Pairing
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.MeasureTheory.Function.Holder

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- Each divergence coordinate pairs an `L¹` function with a bounded continuous function. -/
private lemma integrable_divergencePairingDensity
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable (fun x ↦ f x * admissibleDivergence v x) (domainMeasure Ω) := by
  simp only [admissibleDivergence_def, Finset.mul_sum]
  apply MeasureTheory.integrable_finsetSum
  intro i _
  have hcont : Continuous (fun x ↦
      fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i) := by
    exact (PiLp.continuous_apply (p := 2) (β := fun _ : Fin d ↦ ℝ) i).comp
      ((v.toTestFunction.contDiff.continuous_fderiv_apply (by simp)).comp
        (continuous_id.prodMk continuous_const))
  have hsupp : HasCompactSupport (fun x ↦
      fderiv ℝ v.toTestFunction x (EuclideanSpace.single i (1 : ℝ)) i) :=
    (v.toTestFunction.hasCompactSupport.fderiv_apply ℝ (EuclideanSpace.single i (1 : ℝ))).comp_left
      (g := fun z : EuclideanSpace ℝ (Fin d) ↦ z i) rfl
  exact (MeasureTheory.Lp.memLp f).integrable_mul
    (hcont.memLp_top_of_hasCompactSupport hsupp (domainMeasure Ω))

/-- The weak-gradient pairing is integrable by the `L¹`–`L∞` Hölder inequality. -/
private lemma integrable_weakGradientPairingDensity
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (g : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω))
    (v : AdmissibleTestField Ω) :
    MeasureTheory.Integrable
      (fun x ↦ inner ℝ (g x) (v.toTestFunction x)) (domainMeasure Ω) := by
  exact MeasureTheory.memLp_one_iff_integrable.1 <|
    (innerSL ℝ).memLp_of_bilin 1 (MeasureTheory.Lp.memLp g)
      (v.toTestFunction.continuous.memLp_top_of_hasCompactSupport
        v.toTestFunction.hasCompactSupport (domainMeasure Ω))

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
    intro v
    have hleft : admissibleDivergencePairing (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) v = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards [MeasureTheory.Lp.coeFn_zero ℝ 1 (domainMeasure Ω)] with x hx
      rw [hx]
      exact zero_mul _
    have hright :
        (∫ x, inner ℝ ((0 : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)) x)
          (v.toTestFunction x) ∂domainMeasure Ω) = 0 := by
      apply MeasureTheory.integral_eq_zero_of_ae
      filter_upwards [MeasureTheory.Lp.coeFn_zero (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)]
        with x hx
      rw [hx]
      exact inner_zero_left _
    change admissibleDivergencePairing (0 : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) v =
      -∫ x, inner ℝ ((0 : MeasureTheory.Lp (EuclideanSpace ℝ (Fin d)) 1 (domainMeasure Ω)) x)
        (v.toTestFunction x) ∂domainMeasure Ω
    rw [hleft, hright, neg_zero]
  add_mem' := by
    intro f g hf hg v
    have hleft : admissibleDivergencePairing (f.1 + g.1) v =
        admissibleDivergencePairing f.1 v + admissibleDivergencePairing g.1 v := by
      rw [admissibleDivergencePairing_def, admissibleDivergencePairing_def,
        admissibleDivergencePairing_def, ← MeasureTheory.integral_add
          (integrable_divergencePairingDensity f.1 v) (integrable_divergencePairingDensity g.1 v)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.Lp.coeFn_add f.1 g.1] with x hx
      simp only [hx, Pi.add_apply, add_mul]
    have hright :
        (∫ x, inner ℝ ((f.2 + g.2) x) (v.toTestFunction x) ∂domainMeasure Ω) =
          (∫ x, inner ℝ (f.2 x) (v.toTestFunction x) ∂domainMeasure Ω) +
            ∫ x, inner ℝ (g.2 x) (v.toTestFunction x) ∂domainMeasure Ω := by
      rw [← MeasureTheory.integral_add (integrable_weakGradientPairingDensity f.2 v)
        (integrable_weakGradientPairingDensity g.2 v)]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.Lp.coeFn_add f.2 g.2] with x hx
      simp only [hx, Pi.add_apply, inner_add_left]
    change admissibleDivergencePairing (f.1 + g.1) v =
      -∫ x, inner ℝ ((f.2 + g.2) x) (v.toTestFunction x) ∂domainMeasure Ω
    rw [hleft, hright, hf v, hg v, neg_add]
  smul_mem' := by
    intro a f hf v
    have hleft : admissibleDivergencePairing (a • f.1) v =
        a * admissibleDivergencePairing f.1 v := by
      rw [admissibleDivergencePairing_def, admissibleDivergencePairing_def,
        ← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.Lp.coeFn_smul a f.1] with x hx
      simp only [hx, Pi.smul_apply, smul_eq_mul, mul_assoc]
    have hright :
        (∫ x, inner ℝ ((a • f.2) x) (v.toTestFunction x) ∂domainMeasure Ω) =
          a * ∫ x, inner ℝ (f.2 x) (v.toTestFunction x) ∂domainMeasure Ω := by
      rw [← MeasureTheory.integral_const_mul]
      apply MeasureTheory.integral_congr_ae
      filter_upwards [MeasureTheory.Lp.coeFn_smul a f.2] with x hx
      simp only [hx, Pi.smul_apply, real_inner_smul_left]
    change admissibleDivergencePairing (a • f.1) v =
      -∫ x, inner ℝ ((a • f.2) x) (v.toTestFunction x) ∂domainMeasure Ω
    rw [hleft, hright, hf v, mul_neg]

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
