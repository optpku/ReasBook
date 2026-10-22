/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Theorem_1_11
import RiemannSurfaces_Forster_1981.Chap01.Theorem_1_15

open scoped Manifold OnePoint

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `MeromorphicAt.eventually_eq_zero_or_eventually_ne_zero`,
  `MeromorphicOn.inv`.
- Verified locally: `eq_of_holomorphic_of_eqOn_of_accPt` from Theorem 1.11 and
  `meromorphicToRiemannSphere_holomorphic` from Theorem 1.15.
- Owner choice: express meromorphic identity and zero-set isolation through the canonical
  `OnePoint ℂ`-valued map `meromorphicToRiemannSphere`; expose the field consequence as reciprocal
  closure rather than as a misleading `Subfield` of total `ℂ`-valued functions.
-/

namespace RiemannSurface

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]

/-- Remark 1.16 (1): the identity theorem extends to meromorphic functions on a Riemann surface
after adjoining the value `∞` at poles, so equality on a set with an accumulation point forces
global equality of the associated maps to `ℙ¹(ℂ) = OnePoint ℂ`. -/
theorem eq_meromorphicToRiemannSphere_of_eqOn_of_accPt
    {f₁ f₂ : (⊤ : Opens X) → ℂ} (hf₁ : f₁ ∈ 𝓜((⊤ : Opens X))) (hf₂ : f₂ ∈ 𝓜((⊤ : Opens X)))
    {A : Set X} (hA : Set.EqOn (meromorphicToRiemannSphere f₁) (meromorphicToRiemannSphere f₂) A)
    {a : X} (ha : AccPt a (Filter.principal A)) :
    meromorphicToRiemannSphere f₁ = meromorphicToRiemannSphere f₂ :=
  eq_of_holomorphic_of_eqOn_of_accPt
    (meromorphicToRiemannSphere_holomorphic f₁ hf₁)
    (meromorphicToRiemannSphere_holomorphic f₂ hf₂)
    hA ha

/-- Remark 1.16 (1) in closure form: it is enough that the agreement set contain a point of
`closure (A \ {a})`. -/
theorem eq_meromorphicToRiemannSphere_of_eqOn_of_mem_closure
    {f₁ f₂ : (⊤ : Opens X) → ℂ} (hf₁ : f₁ ∈ 𝓜((⊤ : Opens X))) (hf₂ : f₂ ∈ 𝓜((⊤ : Opens X)))
    {A : Set X} (hA : Set.EqOn (meromorphicToRiemannSphere f₁) (meromorphicToRiemannSphere f₂) A)
    {a : X} (ha : a ∈ closure (A \ {a})) :
    meromorphicToRiemannSphere f₁ = meromorphicToRiemannSphere f₂ :=
  eq_of_holomorphic_of_eqOn_of_mem_closure
    (meromorphicToRiemannSphere_holomorphic f₁ hf₁)
    (meromorphicToRiemannSphere_holomorphic f₂ hf₂)
    hA ha

/-- Remark 1.16 (2): if a global meromorphic function on a Riemann surface is not identically
zero, then its zero set is discrete, equivalently its zeros are isolated. -/
theorem isDiscrete_zeroSet_of_not_identicallyZero (f : (⊤ : Opens X) → ℂ)
    (hf : f ∈ 𝓜((⊤ : Opens X)))
    (h0 : meromorphicToRiemannSphere f ≠ fun _ ↦ ((0 : ℂ) : OnePoint ℂ)) :
    IsDiscrete ((meromorphicToRiemannSphere f) ⁻¹' {((0 : ℂ) : OnePoint ℂ)}) := by
  rw [isDiscrete_iff_nhdsNE]
  intro x hx
  by_contra hnx
  have hacc :
      AccPt x (Filter.principal ((meromorphicToRiemannSphere f) ⁻¹' {((0 : ℂ) : OnePoint ℂ)})) := by
    rw [accPt_principal_iff_nhdsWithin]
    simpa [nhdsWithin, Set.diff_eq, inf_assoc, inf_comm, inf_left_comm, Set.inter_assoc,
      Set.inter_left_comm, Set.inter_comm] using Filter.neBot_iff.mpr hnx
  apply h0
  refine eq_of_holomorphic_of_eqOn_of_accPt
    (meromorphicToRiemannSphere_holomorphic f hf)
    ?_ ?_ hacc
  · simpa [Holomorphic] using
      (mdifferentiable_const :
        MDifferentiable (𝓘(ℂ)) (𝓘(ℂ)) (fun _ : X ↦ ((0 : ℂ) : OnePoint ℂ)))
  · intro y hy
    simpa using hy

/-- Remark 1.16 (3): the reciprocal of a global meromorphic function is meromorphic, hence in
particular the textbook non-identically-zero case needed for the field structure. -/
theorem inv_mem_meromorphicFunctions (f : (⊤ : Opens X) → ℂ)
    (hf : f ∈ 𝓜((⊤ : Opens X))) :
    f⁻¹ ∈ 𝓜((⊤ : Opens X)) := by
  rw [mem_meromorphicFunctions]
  intro x
  simpa [meromorphicAt_iff_coord] using
    _root_.MeromorphicAt.fun_inv ((mem_meromorphicFunctions _ _).mp hf x)

end RiemannSurface
