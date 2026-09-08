module

public import ReasLib.Analysis.Calculus.LocalInvariantGraph.ExplicitContraction.MetricTopSectionFacade
public import ReasLib.Analysis.Calculus.LocalCutoff.GraphJetTransform.HolonomicTopSectionCertificate
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Normed.Module.Multilinear.Curry

public section

noncomputable section

universe u

namespace LocalInvariantGraph

variable {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Infrastructure I.16a: the canonical order-`m + 1` section value obtained
from a scalar derivative value by multilinear embedding and uncurrying. -/
noncomputable def scalarTopSectionValue
    (m : ℕ) (v : X) : (ℝ [×(m + 1)]→L[ℝ] X) :=
  (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (m + 1) ↦ ℝ) X).symm
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) v))

/-- Helper for Infrastructure I.16a: currying the canonical scalar section
recovers the scalar-multiplication map on the embedded derivative value. -/
theorem scalarTopSectionValue_curryLeft (m : ℕ) (v : X) :
    (scalarTopSectionValue m v).curryLeft =
      ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ)
        ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X) v) := by
  exact (continuousMultilinearCurryLeftEquiv ℝ
    (fun _ : Fin (m + 1) ↦ ℝ) X).apply_symm_apply _

/-- Helper for Infrastructure I.16a: the curried scalar section is the
composition of the multilinear embedding with the one-dimensional derivative. -/
theorem scalarTopSectionValue_curryLeft_eq_comp (m : ℕ) (v : X) :
    (scalarTopSectionValue m v).curryLeft =
      ((ContinuousMultilinearMap.piFieldEquiv ℝ (Fin m) X).toContinuousLinearEquiv :
          X →L[ℝ] (ℝ [×m]→L[ℝ] X)).comp
        (ContinuousLinearMap.toSpanSingleton ℝ v) := by
  rw [scalarTopSectionValue_curryLeft]
  apply ContinuousLinearMap.ext
  intro t
  simp only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
    ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    map_smul]

/-- Infrastructure I.16a: scalar top-jet derivative data consists of a continuous
value field and its pointwise derivative for the predecessor iterated derivative. -/
structure ScalarTopJetDerivativeData (ζ : ℝ → X) (r : ℕ) where
  value : ℝ → X
  continuous_value : Continuous value
  derivative : ∀ u, HasDerivAt (iteratedDeriv (r - 1) ζ) (value u) u

/-- Helper for Infrastructure I.16a: a scalar predecessor derivative gives the
bundled holonomic derivative of the corresponding multilinear Taylor section. -/
theorem ScalarTopJetDerivativeData.hasFDerivAt_section
    {ζ : ℝ → X} {r : ℕ}
    (data : ScalarTopJetDerivativeData ζ r) (u : ℝ) :
    HasFDerivAt
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1))
      (scalarTopSectionValue (r - 1) (data.value u)).curryLeft u := by
  have hfunction :
      (fun y ↦ (ftaylorSeries ℝ ζ y) (r - 1)) =
        (fun w : X ↦
          (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin (r - 1)) X) w) ∘
            iteratedDeriv (r - 1) ζ := by
    funext y
    change iteratedFDeriv ℝ (r - 1) ζ y = _
    rw [iteratedFDeriv_eq_equiv_comp]
  have hembed : HasFDerivAt
      (fun w : X ↦
        (ContinuousMultilinearMap.piFieldEquiv ℝ (Fin (r - 1)) X) w)
      ((ContinuousMultilinearMap.piFieldEquiv ℝ
        (Fin (r - 1)) X).toContinuousLinearEquiv :
          X →L[ℝ] (ℝ [×(r - 1)]→L[ℝ] X))
      (iteratedDeriv (r - 1) ζ u) :=
    (ContinuousMultilinearMap.piFieldEquiv ℝ
      (Fin (r - 1)) X).toContinuousLinearEquiv.hasFDerivAt
  have hcomp := hembed.comp u (data.derivative u).hasFDerivAt
  rw [hfunction, scalarTopSectionValue_curryLeft_eq_comp]
  exact hcomp

/-- Helper for Infrastructure I.16a: continuity of a scalar top-jet value
field transports through the canonical multilinear section embedding. -/
theorem continuous_topSectionValue_of_continuous
    (m : ℕ) (v : ℝ → X) (hv : Continuous v) :
    Continuous (fun u ↦ scalarTopSectionValue m (v u)) := by
  unfold scalarTopSectionValue
  fun_prop

/-- Infrastructure I.16a: scalar top-jet derivative data projects to the
holonomic top-section interface used by the successor regularity theorem. -/
noncomputable def ScalarTopJetDerivativeData.toHolonomicTopSectionData
    {ζ : ℝ → X} {r : ℕ}
    (data : ScalarTopJetDerivativeData ζ r) :
    LocalCutoff.GraphTransform.HolonomicTopSectionData ζ r :=
  { value := fun u ↦ scalarTopSectionValue (r - 1) (data.value u)
    continuous_value := continuous_topSectionValue_of_continuous
      (r - 1) data.value data.continuous_value
    derivative := data.hasFDerivAt_section }

/-- Infrastructure I.16a: scalar top-jet derivative data also projects directly
to the metric holonomic certificate consumed by finite-smooth assembly. -/
noncomputable def ScalarTopJetDerivativeData.toMetricHolonomicTopSectionCertificate
    {ζ : ℝ → X} {r : ℕ}
    (data : ScalarTopJetDerivativeData ζ r) :
    MetricHolonomicTopSectionCertificate ζ r :=
  metricHolonomicTopSectionCertificate_of_data data.toHolonomicTopSectionData

end LocalInvariantGraph
