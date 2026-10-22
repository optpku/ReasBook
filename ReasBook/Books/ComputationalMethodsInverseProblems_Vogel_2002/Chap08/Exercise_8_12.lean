/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Exercise_1_14
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap01.Remark_1_1.Fredholm
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4_1.Approximation
public import Mathlib.Analysis.Convex.Extrema

public section

/-!
Exercise 8.12.

The source asks a qualitative question about how the reconstructions in the
one-dimensional test problem of Section 8.3.1 change as `β` increases. The
current repository snapshot still does not provide a checked Lean owner for the
exact discrete Section 8.3.1 datum or for the corresponding `β`-dependent
one-dimensional benchmark objective. Because those missing owners are the
mathematical payload of the exercise, packaging arbitrary minimizer families
and arbitrary comparison relations would weaken the source semantics rather
than preserve them.

Accordingly this item remains a labeled blocker/check-only surface. The checks
below record the verified benchmark ingredients already available upstream: the
Figure 1.1 true solution, the Gaussian midpoint matrix from `(1.3)`, the
Chapter 8 smooth approximation `J_β`, and constrained minimality via
`IsMinOn`.
-/

/- Exercise 8.12. Main labeled source-facing blocker entry.

The future source-faithful benchmark owner for the Section 8.3.1
one-dimensional test problem should build directly on these anchors rather
than introducing a generic reconstruction-family wrapper. -/

#check Fredholm1D.figure11TrueSolution
#check Fredholm1D.midpointMatrix
#check VariationalRegularization.smoothNormApproxTotalVariation
#check
  (IsMinOn :
    (EuclideanSpace ℝ (Fin 1) → EReal) →
      Set (EuclideanSpace ℝ (Fin 1)) →
        EuclideanSpace ℝ (Fin 1) → Prop)
