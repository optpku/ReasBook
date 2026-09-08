module

public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.FixedSectionDerivativeBridge
public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFacade

public section

noncomputable section

open scoped Topology

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Helper for Infrastructure I.16a: the limiting bounded section of a scalar secant
certificate is represented as a one-variable continuous multilinear map. -/
noncomputable def secantCertificateOneSectionValue
    {ζ : ℝ → X}
  (certificate :
      LocalCutoff.GraphTransform.FixedSectionSecantCertificate
        (fun y : ℝ => (ftaylorSeries ℝ ζ y) 0))
    (u : ℝ) : (ℝ [×1]→L[ℝ] X) :=
  ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 1) X
    ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 0) X).symm
      (certificate.scale • certificate.limitSection u))

/-- Helper for Infrastructure I.16a: the curry-left evaluation of the represented section
is the continuous linear map determined by its secant limit. -/
theorem secantCertificateOneSectionValue_curryLeft
    {ζ : ℝ → X}
    (certificate :
      LocalCutoff.GraphTransform.FixedSectionSecantCertificate
        (fun y : ℝ => (ftaylorSeries ℝ ζ y) 0))
    (u : ℝ) :
    (secantCertificateOneSectionValue certificate u).curryLeft =
      ContinuousLinearMap.toSpanSingleton ℝ
        (certificate.scale • certificate.limitSection u) := by
  apply ContinuousLinearMap.ext
  intro t
  apply ContinuousMultilinearMap.ext
  intro z
  have hz : z = (fun _ : Fin 0 => (1 : ℝ)) := Subsingleton.elim _ _
  rw [hz]
  have hinv :
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 0) X).symm
          (certificate.scale • certificate.limitSection u) =
        (certificate.scale • certificate.limitSection u) (fun _ ↦ 1) := by
    rfl
  dsimp only [secantCertificateOneSectionValue]
  rw [hinv]
  simp [ContinuousMultilinearMap.piFieldEquiv,
    ContinuousMultilinearMap.curryLeft_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_smul, mul_comm]

/-- Helper for Infrastructure I.16a: continuity of the represented limiting section follows
from bounded-section continuity and the canonical scalar-source multilinear equivalence. -/
theorem continuous_secantCertificateOneSectionValue
    {ζ : ℝ → X}
    (certificate :
      LocalCutoff.GraphTransform.FixedSectionSecantCertificate
        (fun y : ℝ => (ftaylorSeries ℝ ζ y) 0)) :
    Continuous (secantCertificateOneSectionValue certificate) := by
  have hconst : Continuous (fun _ : ℝ => certificate.scale) := continuous_const
  have hscaled : Continuous (fun u : ℝ =>
      certificate.scale • certificate.limitSection u) :=
    hconst.smul certificate.limitSection.continuous
  have hzero : Continuous (fun u : ℝ =>
      (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 0) X).symm
        (certificate.scale • certificate.limitSection u)) :=
    (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 0) X).symm.continuous.comp hscaled
  exact (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin 1) X).continuous.comp hzero

/-- Helper for Infrastructure I.16a: the represented secant section has the bundled
predecessor derivative required by the order-one holonomic interface. -/
theorem secantCertificateOneSectionValue_hasFDerivAt
    {ζ : ℝ → X}
    (certificate :
      LocalCutoff.GraphTransform.FixedSectionSecantCertificate
        (fun y : ℝ => (ftaylorSeries ℝ ζ y) 0)) :
    ∀ u, HasFDerivAt (fun y ↦ (ftaylorSeries ℝ ζ y) 0)
      (secantCertificateOneSectionValue certificate u).curryLeft u := by
  intro u
  have hderiv := (certificate.hasDerivAt u).hasFDerivAt
  rw [secantCertificateOneSectionValue_curryLeft certificate u]
  exact hderiv

/-- Infrastructure I.16a: a bounded-section secant certificate supplies the order-one
holonomic section data consumed by the metric top-section facade. -/
noncomputable def orderOneHolonomicSectionData_of_fixedSectionSecantCertificate
    {ζ : ℝ → X}
    (certificate :
      LocalCutoff.GraphTransform.FixedSectionSecantCertificate
        (fun y : ℝ => (ftaylorSeries ℝ ζ y) 0)) :
    OrderOneHolonomicSectionData ζ :=
  { value := secantCertificateOneSectionValue certificate
    continuous_value := continuous_secantCertificateOneSectionValue certificate
    derivative := secantCertificateOneSectionValue_hasFDerivAt certificate }

end LocalInvariantGraph
