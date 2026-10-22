/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic

public section

/- Definition 2.32.

For a real Hilbert space functional `J : H → ℝ`, mathlib already formalizes
the source gradient `grad J(f)` as `gradient J f`, and its Riesz
representation formula is already the canonical theorem `inner_gradient_left`.
That theorem states the same identity as the source display, with the two sides
written in the opposite order.
-/

#check gradient
#check inner_gradient_left
