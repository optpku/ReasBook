/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_9

public section

noncomputable section

namespace VariationalRegularization

variable {d : ℕ}

/-- Helper for Definition 8.14: an `L¹(Ω)` function is BV-admissible when its
Chapter 8 BV quantity `‖f‖ + totalVariation f` is finite in `EReal`. -/
@[expose]
def IsBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) : Prop :=
  ((‖f‖ : ℝ) : EReal) + totalVariation f < ⊤

/-- Definition 8.14. The Chapter 8 bounded-variation space on the canonical
`L¹(Ω)` carrier. -/
@[expose]
def BV
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :=
  {f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω) // IsBV f}

/-- Helper for Definition 8.14: the defining finiteness criterion for `IsBV`. -/
theorem isBV_iff
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω)) :
    IsBV f ↔ ((‖f‖ : ℝ) : EReal) + totalVariation f < ⊤ := by
  -- Expose `IsBV` exactly as its defining finiteness inequality.
  rfl

/-- The source-facing notation for the bounded-variation space over `Ω`. -/
notation "BV(" Ω ")" => BV Ω

namespace BV

/-- Helper for Definition 8.14: construct a bounded-variation element from its
underlying `L¹(Ω)` datum and BV finiteness witness. -/
@[expose]
def ofLp
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (hf : IsBV f) :
    BV Ω :=
  ⟨f, hf⟩

/-- Helper for Definition 8.14: the underlying canonical `L¹(Ω)` element of a
bounded-variation function. -/
@[expose]
def toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) :
    MeasureTheory.Lp ℝ 1 (domainMeasure Ω) :=
  u.1

/-- Helper for Definition 8.14: `ofLp` recovers the supplied `L¹(Ω)` datum. -/
theorem ofLp_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (f : MeasureTheory.Lp ℝ 1 (domainMeasure Ω))
    (hf : IsBV f) :
    (ofLp f hf).toL1 = f := by
  -- The constructor stores `f` as the subtype's first projection.
  rfl

/-- Helper for Definition 8.14: the underlying `L¹(Ω)` datum of a bounded-variation
element satisfies the BV finiteness condition. -/
theorem isBV_toL1
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) :
    IsBV u.toL1 := by
  -- Transport the stored subtype witness to the projection `u.toL1`.
  simpa [toL1] using u.2

end BV

/-- Helper for Definition 8.14: the Chapter 8 BV norm on `BV(Ω)` given by
`EReal.toReal` of the source quantity
`((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1`. -/
instance instNormBV
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    Norm (BV Ω) where
  norm u := ((((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1).toReal)

namespace BV

/-- Helper for Definition 8.14: the defining formula for the Chapter 8 BV norm. -/
theorem norm_def
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) :
    ‖u‖ = ((((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1).toReal) := by
  -- Unfold the `Norm` instance once to expose the declared BV norm formula.
  rfl

/-- Helper for Definition 8.14: every bounded-variation element has finite
Chapter 8 BV quantity. -/
theorem norm_add_totalVariation_lt_top
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (u : BV Ω) :
    ((‖u.toL1‖ : ℝ) : EReal) + totalVariation u.toL1 < ⊤ := by
  -- Re-express the stored BV witness as the explicit finiteness inequality.
  simpa [IsBV] using isBV_toL1 u

end BV

end VariationalRegularization
