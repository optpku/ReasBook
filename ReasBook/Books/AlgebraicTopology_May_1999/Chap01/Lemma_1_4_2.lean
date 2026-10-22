/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

noncomputable section

open scoped ContinuousMap

variable {X : Type u} [TopologicalSpace X]
variable {Y : Type v} [TopologicalSpace Y]
variable {Z : Type w} [TopologicalSpace Z]

/-- Lemma 1.4.2 (1): the map on fundamental groups induced by the identity map is the identity
homomorphism. -/
-- Proof sketch: every loop class is represented by a loop `p : Path x x`, and both sides send the
-- class of `p` to itself by definition.
theorem fundamental_group_map_id (x : X) :
    FundamentalGroup.map (.id X) x = MonoidHom.id (FundamentalGroup X x) := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro p
  rfl

/-- Lemma 1.4.2 (2): the map on fundamental groups induced by a composite `q ∘ p` is the
composite of the induced homomorphisms `q_*` and `p_*`. -/
-- Proof sketch: on a representative loop `r : Path x x`, both sides are definitionally the class
-- of the composite path map `(q ∘ p) ∘ r`.
theorem fundamental_group_map_comp (p : C(X, Y)) (q : C(Y, Z)) (x : X) :
    FundamentalGroup.map (q.comp p) x =
      (FundamentalGroup.map q (p x)).comp (FundamentalGroup.map p x) := by
  ext γ
  refine Quotient.inductionOn γ ?_
  intro r
  rfl
