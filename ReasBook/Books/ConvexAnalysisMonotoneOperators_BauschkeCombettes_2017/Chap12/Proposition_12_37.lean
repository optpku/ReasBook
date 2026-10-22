/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap09.Proposition_9_30
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Definition_12_1
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap12.Proposition_12_36

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u

namespace ERealFunction

variable {H : Type u} [AddCommGroup H]

-- Proof sketch: `f ⊕ g` is the project owner for the separable sum `(y, z) ↦ f y + g z`, and
-- `Prod.fst + Prod.snd` is the canonical product-sum map.
-- The fiber over `x` is parameterized by `y ↦ (y, x - y)`, so the defining `sInf` is exactly the
-- infimum in the infimal-convolution formula.
/-- Proposition 12.37: infimal convolution is the infimal postcomposition of the separable sum
`(y, z) ↦ f y + g z` by the product-sum map `(y, z) ↦ y + z`. -/
theorem infimalConvolution_eq_infimalPostcomposition_separableSum
    (f g : H → Set.Ioi (⊥ : EReal)) :
    infimalConvolution f.asEReal g.asEReal = (Prod.fst + Prod.snd) ▷ (f ⊕ g) := by
  ext x
  change (⨅ y : H, (f y : EReal) + (g (x - y) : EReal)) = _
  rw [show ((Prod.fst + Prod.snd) ▷ (f ⊕ g)) x =
      sInf ((fun yz : H × H ↦ ((f ⊕ g) yz : EReal)) '' ((Prod.fst + Prod.snd) ⁻¹' {x})) by
      simpa using infimalPostcomposition_apply (Prod.fst + Prod.snd) (f ⊕ g) x]
  rw [show
      (fun yz : H × H ↦ ((f ⊕ g) yz : EReal)) '' ((Prod.fst + Prod.snd) ⁻¹' {x}) =
        Set.range (fun y : H ↦ (f y : EReal) + (g (x - y) : EReal)) from by
      ext t
      constructor
      · rintro ⟨⟨y, z⟩, hyz, rfl⟩
        refine ⟨y, ?_⟩
        have hz : z = x - y := eq_sub_of_add_eq (by simpa [add_comm] using hyz)
        simp [hz]
      · rintro ⟨y, rfl⟩
        refine ⟨(y, x - y), by simp, ?_⟩
        simp]
  exact
    (sInf_range :
      sInf (Set.range (fun y : H ↦ (f y : EReal) + (g (x - y) : EReal))) =
        ⨅ y : H, (f y : EReal) + (g (x - y) : EReal)).symm

end ERealFunction
