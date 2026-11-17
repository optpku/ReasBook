/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import DFPWolfe.V21.CenterManifold
public import DFPWolfe.V21.CenterInterpolation
public import DFPWolfe.Latest.CenterDesign

/-!
# Proposition 8 — the independent alternating center-manifold recurrence

Historical source label: `cm-center-proposition`; this module is preserved from the preceding manuscript revision and is not imported by `DFPWolfe.Latest.Paper`.
The exact spectral recurrence has derivative eigenvalues `1`, `−1/9`, `0`,
a locally invariant C⁷ graph, the source cubic graph coefficients `198/5`
and `8`, and inverse-cubic slow scale. Its literal initialized trajectory
has positive definite matrices at every stage.

The following Section 6 entries retain the same physical recurrence,
two-step center cancellation, limiting amplitude, full limiting circle,
and conditional explicit interpolation. The new quadratic endpoint entry
proves the phase decreases `2/3`, `5/6` and endpoint Wolfe inequalities
before imposing any interpolation-support separation condition.
The two constructions are independent; they need not produce the same orbit.
The general-control design entry derives the cubic and quintic cancellation
coefficients from two attached actual spectral steps, including the first
step's eigenbasis rotation. Its existence and validity follow from the source
limits before fixing shape two and the control ratio minus two.
-/
