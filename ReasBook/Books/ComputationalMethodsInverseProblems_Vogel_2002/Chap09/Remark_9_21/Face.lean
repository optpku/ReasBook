/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap09.Definition_9_2.IndexSets
public import Mathlib.Data.Set.Operations

public section

namespace ActiveSet

universe u v

variable {H : Type u} {ι : Type v}

/-- The face associated with `f` inside the feasible set `C`, obtained by
enforcing vanishing of the active constraints from equation `(9.33)`. -/
def face (C : Set H) (c : ι → H → ℝ) (f : H) : Set H :=
  {v | v ∈ C ∧ ∀ i ∈ active c f, c i v = 0}

/-- Membership in `face C c f` means feasible-set membership together with
vanishing on every active constraint at `f`. -/
theorem mem_face (C : Set H) (c : ι → H → ℝ) (f v : H) :
    v ∈ face C c f ↔ v ∈ C ∧ ∀ i ∈ active c f, c i v = 0 :=
  Iff.rfl

/-- Equal active sets determine the same associated face. -/
theorem face_eq_of_activeSet_eq (C : Set H) (c : ι → H → ℝ) {f g : H}
    (hfg : active c f = active c g) :
    face C c f = face C c g := by
  ext v
  simp [face, hfg]

end ActiveSet
