/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap07.Definition_7_4.Curve

public section

/- Exercise 7.7. Main labeled source-facing canonical-reuse entry.

Recovered Chapter 7 source context places Exercise 7.7 immediately after the
generic L-curve derivation in §7.4: after defining `R(α) = ‖r_α‖^2` and
`S(α) = ‖f_α‖^2`, equation `(7.32)` is the displayed energy-only curvature
formula in terms of `R`, `S`, and `deriv S`.

The canonical owner for that source-facing formula is
`LCurve.curvatureFromEnergies`, and the displayed equation `(7.32)` itself is
the companion definitional theorem `LCurve.curvatureFromEnergies_def`.
-/

#check LCurve.curvatureFromEnergies

#check LCurve.curvatureFromEnergies_def

end
