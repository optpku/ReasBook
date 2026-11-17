module

public import DFPWolfe.Latest.Main
public import ReasLib.Optimization.DFP.Polar.General.SequenceAsymptotics

public section

noncomputable section

namespace DFPWolfe.Latest

open DFP.Polar.General

/-!
# Comparisons on the same actual Wolfe orbit

The unnumbered comparisons in `sec:known-results` and following
`lem:planar-degeneration` concern the very source retained by Theorem 10.
The packages below include gradient-norm oscillation with both quadratic
remainder bounds, infinite total step length, Xu's phase equivalents and
failure of eventual nonincrease, nonzero accepted-endpoint derivatives,
the curvature limit, determinant and free-coefficient equivalents, and
failure of iterate convergence. No separate comparison orbit is selected.
-/

/-- Helper for sec:known-results and lem:planar-degeneration: every actual
planar construction retained by Theorem 10 satisfies all source and canonical
sequence comparisons on its own objective, points, gradients and matrices. -/
theorem PlanarConstruction.sequenceProperties {c1 c2 β ε : ℝ}
    (s : PlanarConstruction c1 c2 β ε) (hβ : β ∈ Set.Ioo 0 1) :
    SequenceAsymptotics.SequenceProperties (s.parameters.withStartIndex s.startIndex) ∧
      SequenceAsymptotics.CanonicalSequenceProperties
        (s.parameters.withStartIndex s.startIndex) s.certificate := by
  have hbeta : 0 < s.parameters.beta := by
    rw [s.beta_eq]
    exact hβ.1
  have hbetaOne : s.parameters.beta < 1 := by
    rw [s.beta_eq]
    exact hβ.2
  obtain ⟨B, _, K, _, c, _, U, _, a, _, b, _, sep, hsep, V, _, hgeometry⟩ :=
    s.sourceData.actualGeometry
  exact SequenceAsymptotics.sameOrbitSequenceProperties_of_geometry
    hgeometry hbeta hbetaOne s.startIndex_pos hsep s.sourceIdentity

/-- Helper for thm:main and sec:known-results: every admissible Wolfe pair,
Hessian accuracy and Hölder exponent has one actual planar counterexample
carrying the complete comparison conclusions of the latest manuscript. -/
theorem planarCounterexampleWithSequenceProperties (c1 c2 ε β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ s : PlanarConstruction c1 c2 β ε,
      SequenceAsymptotics.SequenceProperties (s.parameters.withStartIndex s.startIndex) ∧
        SequenceAsymptotics.CanonicalSequenceProperties
          (s.parameters.withStartIndex s.startIndex) s.certificate := by
  obtain ⟨s⟩ := planarSource c1 c2 ε β hc1 hc12 hc2 hε hβ
  exact ⟨s, s.sequenceProperties hβ⟩

/-- Helper for thm:main and sec:known-results: the arbitrary-dimensional
counterexample is the literal identity-block extension of the same planar
source carrying all sequence comparisons. Its objective properties and the
source-to-certificate identities are retained together. -/
theorem mainWithSequenceProperties (n : ℕ) (hn : 2 ≤ n) (c1 c2 ε β : ℝ)
    (hc1 : 0 < c1) (hc12 : c1 < c2) (hc2 : c2 < 1)
    (hε : ε ∈ Set.Ioo 0 1) (hβ : β ∈ Set.Ioo 0 1) :
    ∃ s : PlanarConstruction c1 c2 β ε,
      ∃ w : DFP.StrongWolfeCounterexample (Fin n) (1 / 2) (3 / 2)
        (s.parameters.withStartIndex s.startIndex).c1 (s.parameters.withStartIndex s.startIndex).c2,
        DFP.Polar.OrthogonalExtension.FinExtensionIdentity n hn s.certificate w ∧
          Transport.CounterexampleProperties s.parameters.beta ε w
            (DFP.Polar.OrthogonalExtension.planeEmbedding n hn) ∧
          SequenceAsymptotics.SequenceProperties (s.parameters.withStartIndex s.startIndex) ∧
          SequenceAsymptotics.CanonicalSequenceProperties
            (s.parameters.withStartIndex s.startIndex) s.certificate := by
  obtain ⟨s, w, hsource, hproperties⟩ :=
    mainWithSource n hn c1 c2 ε β hc1 hc12 hc2 hε hβ
  exact ⟨s, w, hsource, hproperties, s.sequenceProperties hβ⟩

end DFPWolfe.Latest
