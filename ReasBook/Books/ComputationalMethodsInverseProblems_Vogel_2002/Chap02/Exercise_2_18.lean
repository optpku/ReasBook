/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_26

public section

/-!
Exercise 2.18. Source-facing blocker.

The current workspace exposes the canonical owners `ConvexOn` and
`weakLowerSemicontinuous`, together with the bridge
`weakLowerSemicontinuous_of_lowerSemicontinuousWeakSpace`. However, the
available repository snapshot does not justify the missing extra hypothesis
needed to derive weak lower semicontinuity from bare `ConvexOn ℝ Set.univ J`.

In particular, the local mathlib theorem `ConvexOn.continuousOn` is only
available under a finite-dimensional hypothesis, so this file cannot honestly
assert the stronger implication for an arbitrary real Hilbert space. The item
therefore remains blocked until the source confirms the intended additional
assumption.
-/

/- Exercise 2.18. Main labeled source-facing blocker entry.

The source-facing theorem cannot yet be stated faithfully as a proved Lean
declaration, because the current source snapshot omits the additional
hypothesis that turns convexity into a valid weak-lower-semicontinuity
statement. The checks below record the exact canonical owners and bridge that
the eventual repair should reuse, rather than keeping a false local theorem.
-/
#check ConvexOn
#check weakLowerSemicontinuous
#check weakLowerSemicontinuous_of_lowerSemicontinuousWeakSpace
