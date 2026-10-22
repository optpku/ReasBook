/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Geometry.Euclidean.Volume.Measure
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.Topology.Sets.Opens

public section

noncomputable section

namespace VariationalRegularization

open scoped BigOperators

variable {d : ℕ}

/-- The restricted volume measure on an open domain `Ω ⊆ ℝ^d`. -/
@[expose]
def domainMeasure (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
    MeasureTheory.Measure (EuclideanSpace ℝ (Fin d)) :=
  (MeasureTheory.Measure.euclideanHausdorffMeasure d :
      MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
    (Ω : Set (EuclideanSpace ℝ (Fin d)))

/-- The defining restricted-volume formula for `domainMeasure`. -/
theorem domainMeasure_def (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
    domainMeasure Ω =
      (MeasureTheory.Measure.euclideanHausdorffMeasure d :
          MeasureTheory.Measure (EuclideanSpace ℝ (Fin d))).restrict
        (Ω : Set (EuclideanSpace ℝ (Fin d))) := rfl

/-- A compactly supported `C¹` vector field on `Ω` with pointwise norm at most `1` on `Ω`. -/
structure AdmissibleTestField (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) where
  /-- The underlying compactly supported `C¹` vector field on `Ω`. -/
  toTestFunction : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1
  /-- The pointwise norm bound on `Ω`. -/
  norm_le_one :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖toTestFunction x‖ ≤ 1

namespace AdmissibleTestField

/-- Build an admissible test field from a bundled `TestFunction` and the source norm bound. -/
@[expose]
def ofTestFunction
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)
    (h_norm : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖v x‖ ≤ 1) :
    AdmissibleTestField Ω :=
  { toTestFunction := v
    norm_le_one := h_norm }

/-- `ofTestFunction` recovers the supplied bundled test function. -/
theorem ofTestFunction_toTestFunction
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1)
    (h_norm : ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖v x‖ ≤ 1) :
    (ofTestFunction v h_norm).toTestFunction = v := rfl

/-- The source-facing admissibility data carried by an `AdmissibleTestField`. -/
theorem spec
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))}
    (v : AdmissibleTestField Ω) :
    ContDiff ℝ 1 v.toTestFunction ∧
      HasCompactSupport v.toTestFunction ∧
      tsupport v.toTestFunction ⊆ (Ω : Set (EuclideanSpace ℝ (Fin d))) ∧
      (∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))), ‖v.toTestFunction x‖ ≤ 1) := by
  exact ⟨v.toTestFunction.contDiff, v.toTestFunction.hasCompactSupport,
    v.toTestFunction.tsupport_subset, v.norm_le_one⟩

/-- The zero test field satisfies the admissibility norm bound. -/
theorem zero_norm_le_one
    {Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))} :
    ∀ x ∈ (Ω : Set (EuclideanSpace ℝ (Fin d))),
      ‖(0 : TestFunction Ω (EuclideanSpace ℝ (Fin d)) 1) x‖ ≤ 1 := by
  intro x _
  simp

/-- The zero compactly supported `C¹` vector field is admissible. -/
@[expose]
def zero
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
    AdmissibleTestField Ω :=
  { toTestFunction := 0
    norm_le_one := zero_norm_le_one }

/-- The underlying test function of `zero` is `0`. -/
theorem zero_toTestFunction
    (Ω : TopologicalSpace.Opens (EuclideanSpace ℝ (Fin d))) :
    (zero Ω).toTestFunction = 0 := rfl

end AdmissibleTestField

end VariationalRegularization
