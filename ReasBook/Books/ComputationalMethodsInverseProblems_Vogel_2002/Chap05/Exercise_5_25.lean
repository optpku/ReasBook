/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Data.Complex.Basic
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Definition_5_27.BCCB
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap05.Prop_5_28.HTTB

public section

open scoped Matrix

/- Exercise 5.25. When the PSF is already recorded on the image grid as an
`n_x × n_y` array `t`, the direct backend is the existing BCCB operator
`Matrix.bccb t`. The older odd-size `(2 * n_x - 1) × (2 * n_y - 1)` kernel path
through `Matrix.periodicExtension` and `Matrix.httb` is replaced by the exact
bridge `Matrix.httb_periodicExtension_eq_bccb`, so the image-space action is
recorded by `Matrix.of (fun i j ↦ ((Matrix.bccb t) *ᵥ f.vec) (j, i))`. -/
#check Matrix.bccb

#check Matrix.httb_periodicExtension_eq_bccb

#check Matrix.of

#check (fun {n_x n_y : ℕ} (t f : Matrix (Fin n_x) (Fin n_y) ℂ) ↦
  Matrix.of fun i j ↦ ((Matrix.bccb t) *ᵥ f.vec) (j, i))
