/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.General.Objective

/-!
# Lemma 9 — explicit interpolation with a prescribed Hölder exponent

Source label: `lem:polar-interpolation` in the manuscript `20251117-DFP/arXiv.tex`.
The source's explicit smooth cutoff realizes all prescribed endpoint jets.
The infinite correction sum is globally C² with a globally `β`-Hölder
Hessian; its value, gradient and Hessian vanish on the limiting circle.
The Hessian error has the source's `Cobj τ₀^β` bound. The final existence
entry proves the geometry and estimates for the actual recurrence.
-/

#check DFP.Polar.General.Objective.existsSourceObjectiveData
#check DFP.Polar.General.InterpolationBounds.exists_norm_hessian_correction_sub_le
