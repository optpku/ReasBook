/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

variable {E : Type u} {F : Type v} [PseudoMetricSpace E] [PseudoMetricSpace F]

/- Definition 13.8: the fixed-constant Lipschitz class `Lip_K(E; F)` is canonically the mathlib
predicate `LipschitzWith K` on maps `E → F`. -/
#check LipschitzWith

/- The textbook distance-inequality formulation of `Lip_K(E; F)` is the canonical theorem
`lipschitzWith_iff_dist_le_mul`. -/
recall lipschitzWith_iff_dist_le_mul

-- Proof sketch: if `f` is `K`-Lipschitz, then it is also `(K + 1)`-Lipschitz, giving a positive
-- Lipschitz constant. Conversely, a positive Lipschitz constant is in particular a Lipschitz
-- constant.
/-- Definition 13.8: a map lies in `Lip(E; F)` exactly when it is Lipschitz with some positive
constant. -/
theorem exists_lipschitzWith_iff {f : E → F} :
    (∃ K : NNReal, LipschitzWith K f) ↔
      ∃ K : NNReal, 0 < K ∧ LipschitzWith K f := by
  constructor
  · rintro ⟨K, hK⟩
    exact ⟨K + 1, by positivity, hK.weaken (le_add_of_nonneg_right zero_le_one)⟩
  · rintro ⟨K, -, hK⟩
    exact ⟨K, hK⟩
