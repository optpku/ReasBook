/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f0dee1064101ffc85a871f8c7f3a997668f5a83b:ReasBook/Papers/DFP_wolfe_local/README.md (Contributors).
-/

module

public import ReasLib.Optimization.DFP.Polar.General.PhysicalRecurrence

/-!
# Polar direction update

Source label: `lem:polar-direction-update` in `20251117-DFP/arXiv.tex`.
The physical matrix recurrence is recovered from the normalized state and its
one-step DFP matrix identity is available as `matrix_step`.
-/

#check DFP.Polar.General.Parameters.matrix_step
