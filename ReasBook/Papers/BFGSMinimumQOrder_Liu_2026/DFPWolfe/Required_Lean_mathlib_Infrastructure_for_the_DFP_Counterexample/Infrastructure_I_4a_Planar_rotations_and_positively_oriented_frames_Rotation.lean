/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_4a_Planar_rotations_and_positively_oriented_frames_Rotation.lean
-/

module

public import ReasLib.Geometry.Euclidean.Plane.Rotation

#check (EuclideanPlane.frame :
  EuclideanSpace ℝ (Fin 2) → Matrix (Fin 2) (Fin 2) ℝ)
