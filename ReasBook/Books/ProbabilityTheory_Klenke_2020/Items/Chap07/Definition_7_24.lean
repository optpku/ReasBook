/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

variable (W : Set V)

/- Definition 7.24: For a subset `W` of a real inner product space, its orthogonal complement is
the canonical submodule `(Submodule.span ℝ W)ᗮ`, i.e. the orthogonal complement of the span of
`W`. -/
#check ((Submodule.span ℝ W)ᗮ : Submodule ℝ V)

variable {W : Set V}

/-- A vector lies in the canonical orthogonal-complement submodule of `W` exactly when it is
orthogonal to every vector in `W`. -/
theorem mem_orthogonal_complement_iff {W : Set V} {v : V} :
    v ∈ (Submodule.span ℝ W)ᗮ ↔ ∀ w ∈ W, inner ℝ v w = 0 := by
  rw [(Submodule.span ℝ W).mem_orthogonal' v]
  constructor
  · intro hv w hw
    exact hv w <| Submodule.subset_span hw
  · intro hv u hu
    induction hu using Submodule.span_induction with
    | mem w hw => exact hv w hw
    | zero => simp
    | add x y _ _ hx hy => simp [inner_add_right, hx, hy]
    | smul c x _ hx => simp [inner_smul_right, hx]
