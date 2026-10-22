/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Maps.Basic

public section

noncomputable section

universe u v

namespace OperatorEquation

variable {H₁ : Type u} {H₂ : Type v}
variable [TopologicalSpace H₁] [TopologicalSpace H₂]

/-- The operator equation `K f = g` is well-posed when every `g` has a unique solution `f` and
the inverse response `g ↦ f` is continuous. -/
structure WellPosed (K : H₁ → H₂) : Prop where
  /-- Every datum `g` admits a solution of `K f = g`. -/
  surjective : Function.Surjective K
  /-- The solution of `K f = g` is unique. -/
  injective : Function.Injective K
  /-- The inverse response to perturbations in `g` is continuous. -/
  continuousInverse :
    Continuous ((Equiv.ofBijective K ⟨injective, surjective⟩).symm)

namespace WellPosed

variable {K : H₁ → H₂}

/-- The underlying bijection determined by a well-posed operator equation. -/
def toEquiv (hK : WellPosed K) : H₁ ≃ H₂ :=
  Equiv.ofBijective K ⟨hK.injective, hK.surjective⟩

/-- The inverse map supplied by a well-posed operator equation. -/
def inverse (hK : WellPosed K) : H₂ → H₁ :=
  hK.toEquiv.symm

/-- A well-posed operator equation has a bijective forward operator. -/
theorem bijective (hK : WellPosed K) : Function.Bijective K :=
  ⟨hK.injective, hK.surjective⟩

/-- The inverse supplied by a well-posed operator equation is continuous. -/
theorem continuous_inverse (hK : WellPosed K) : Continuous hK.inverse := by
  simpa [inverse, toEquiv] using hK.continuousInverse

/-- Applying `K` to the chosen inverse recovers the prescribed datum. -/
theorem apply_inverse (hK : WellPosed K) (g : H₂) : K (hK.inverse g) = g :=
  hK.toEquiv.apply_symm_apply g

/-- Applying the chosen inverse to `K f` recovers `f`. -/
theorem inverse_apply (hK : WellPosed K) (f : H₁) : hK.inverse (K f) = f :=
  hK.toEquiv.symm_apply_apply f

/-- A well-posed operator equation is surjective onto the whole codomain. -/
theorem range_eq_univ (hK : WellPosed K) : Set.range K = Set.univ := by
  ext g
  constructor
  · intro _
    trivial
  · intro _
    rcases hK.surjective g with ⟨f, rfl⟩
    exact ⟨f, rfl⟩

/-- If the forward operator is continuous, a well-posed operator equation determines a
homeomorphism. -/
def toHomeomorph (hK : WellPosed K) (hK_cont : Continuous K) : H₁ ≃ₜ H₂ where
  toEquiv := hK.toEquiv
  continuous_toFun := hK_cont
  continuous_invFun := hK.continuous_inverse

/-- A continuous well-posed operator equation is a homeomorphism. -/
theorem isHomeomorph (hK : WellPosed K) (hK_cont : Continuous K) : IsHomeomorph K :=
  (hK.toHomeomorph hK_cont).isHomeomorph

/-- A homeomorphism is well-posed as an operator equation. -/
theorem ofIsHomeomorph {K : H₁ → H₂} (hK : IsHomeomorph K) : WellPosed K where
  surjective := hK.surjective
  injective := hK.injective
  continuousInverse := by
    change Continuous ((Equiv.ofBijective K hK.bijective).symm)
    simpa [IsHomeomorph.homeomorph] using hK.homeomorph.continuous_invFun

end WellPosed

/-- A map is well-posed exactly when it admits a continuous two-sided inverse. -/
theorem wellPosed_iff_exists_continuousInverse {K : H₁ → H₂} :
    WellPosed K ↔ ∃ g : H₂ → H₁,
      Continuous g ∧ Function.LeftInverse g K ∧ Function.RightInverse g K := by
  constructor
  · intro hK
    exact ⟨hK.inverse, hK.continuous_inverse, hK.inverse_apply, hK.apply_inverse⟩
  · rintro ⟨g, hg_cont, hg_left, hg_right⟩
    refine ⟨?_, ?_, ?_⟩
    · intro y
      exact ⟨g y, hg_right y⟩
    · intro x y hxy
      calc
        x = g (K x) := (hg_left x).symm
        _ = g (K y) := by simp [hxy]
        _ = y := hg_left y
    · have hbij : Function.Bijective K := by
        refine ⟨?_, ?_⟩
        · intro x y hxy
          calc
            x = g (K x) := (hg_left x).symm
            _ = g (K y) := by simp [hxy]
            _ = y := hg_left y
        · intro y
          exact ⟨g y, hg_right y⟩
      have hsymm : (Equiv.ofBijective K hbij).symm = g := by
        funext y
        apply hbij.injective
        calc
          K ((Equiv.ofBijective K hbij).symm y) = y := (Equiv.ofBijective K hbij).apply_symm_apply y
          _ = K (g y) := (hg_right y).symm
      exact hsymm.symm ▸ hg_cont

/-- If `K` is continuous, well-posedness is equivalent to `K` being a homeomorphism. -/
theorem wellPosed_iff_isHomeomorph {K : H₁ → H₂} (hK : Continuous K) :
    WellPosed K ↔ IsHomeomorph K :=
  ⟨fun h ↦ h.isHomeomorph hK, WellPosed.ofIsHomeomorph⟩

/-- An operator equation is ill-posed when it is not well-posed. -/
abbrev illPosed (K : H₁ → H₂) : Prop := ¬ WellPosed K

/-- An operator equation is ill-posed exactly when it is not well-posed. -/
theorem illPosed_iff_not_wellPosed {K : H₁ → H₂} :
    illPosed K ↔ ¬ WellPosed K :=
  Iff.rfl

end OperatorEquation
