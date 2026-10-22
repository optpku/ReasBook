/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Definition_1_12
import RiemannSurfaces_Forster_1981.Chap01.Example_1_5
import Mathlib.Topology.DiscreteSubset

open scoped Manifold OnePoint
open TopologicalSpace

universe u

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `MeromorphicAt`, `OnePoint`, `isDiscrete_iff_forall_exists_isOpen`.
- Verified locally: `RiemannSurface.Holomorphic`, `RiemannSurface.MeromorphicOn`,
  `RiemannSurface.IsPoleAt`, `OnePoint.elim`, and the chapter's `RiemannSurface (OnePoint ℂ)`
  instance from `Example_1_5`.
- Owner choice: model `ℙ¹(ℂ)` as `OnePoint ℂ`, make the forward direction an explicit pole-to-`∞`
  map attached to a global meromorphic function, and express the converse on the open finite locus
  together with the extracted complex-valued finite part.
-/

namespace RiemannSurface

variable {X : Type u} [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X]

/-- A global meromorphic function on a Riemann surface gives a map to the Riemann sphere by sending
its poles to `∞` and keeping its finite values elsewhere. -/
def meromorphicToRiemannSphere (f : (⊤ : Opens X) → ℂ) : X → OnePoint ℂ :=
  letI : DecidablePred (fun x : X ↦ IsPoleAt f ⟨x, Set.mem_univ x⟩) := Classical.decPred _
  fun x ↦
    if _ : IsPoleAt f ⟨x, Set.mem_univ x⟩ then
      (∞ : OnePoint ℂ)
    else
      (f ⟨x, Set.mem_univ x⟩ : OnePoint ℂ)

/-- At a pole, `meromorphicToRiemannSphere` takes the value `∞`. -/
theorem meromorphicToRiemannSphere_apply_of_isPoleAt (f : (⊤ : Opens X) → ℂ) (x : X)
    (hx : IsPoleAt f ⟨x, Set.mem_univ x⟩) :
    meromorphicToRiemannSphere f x = (∞ : OnePoint ℂ) := by
  classical
  simp [meromorphicToRiemannSphere, hx]

/-- Away from poles, `meromorphicToRiemannSphere` agrees with the original complex-valued
function. -/
theorem meromorphicToRiemannSphere_apply_of_not_isPoleAt (f : (⊤ : Opens X) → ℂ) (x : X)
    (hx : ¬ IsPoleAt f ⟨x, Set.mem_univ x⟩) :
    meromorphicToRiemannSphere f x = (f ⟨x, Set.mem_univ x⟩ : OnePoint ℂ) := by
  classical
  simp [meromorphicToRiemannSphere, hx]

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- The finite locus of a map to the Riemann sphere is the complement of its `∞`-fiber. -/
def finitePartSet (f : X → OnePoint ℂ) : Set X :=
  f ⁻¹' ({(∞ : OnePoint ℂ)}ᶜ)

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Membership in the finite locus means that the map does not take the value `∞`. -/
theorem mem_finitePartSet (f : X → OnePoint ℂ) (x : X) :
    x ∈ finitePartSet f ↔ f x ≠ (∞ : OnePoint ℂ) :=
  Iff.rfl

omit [RiemannSurface X] in
/-- The finite locus of a holomorphic map to the Riemann sphere, viewed as an open subset of the
source Riemann surface. -/
def finitePartDomain (f : X → OnePoint ℂ) (hf : Holomorphic f) : Opens X :=
  ⟨finitePartSet f, by
    simpa [finitePartSet] using
      (isOpen_compl_singleton.preimage (holomorphic_continuous hf))⟩

omit [RiemannSurface X] in
/-- Membership in `finitePartDomain f hf` means that the map does not take the value `∞`. -/
theorem mem_finitePartDomain (f : X → OnePoint ℂ) (hf : Holomorphic f) (x : X) :
    x ∈ finitePartDomain f hf ↔ f x ≠ (∞ : OnePoint ℂ) :=
  mem_finitePartSet f x

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- On the finite locus of a holomorphic map to the Riemann sphere, the map has a canonical
complex-valued finite part. -/
def finitePart (f : X → OnePoint ℂ) : finitePartSet f → ℂ :=
  fun x ↦ (f x.1).elim 0 (fun z : ℂ ↦ z)

omit [TopologicalSpace X] [ChartedSpace ℂ X] [RiemannSurface X] in
/-- Re-embedding the finite part into `OnePoint ℂ` recovers the original map on the finite
locus. -/
theorem finitePart_coe (f : X → OnePoint ℂ) (x : finitePartSet f) :
    ((finitePart f x : ℂ) : OnePoint ℂ) = f x.1 := by
  cases hfx : f x.1 using OnePoint.rec with
  | infty =>
      exact (x.2 hfx).elim
  | coe z =>
      simp [finitePart, hfx]

/-- Theorem 1.15 (1): a global meromorphic function on a Riemann surface becomes a holomorphic map
to `ℙ¹(ℂ) = OnePoint ℂ` once each pole is assigned the value `∞`. -/
theorem meromorphicToRiemannSphere_holomorphic (f : (⊤ : Opens X) → ℂ)
    (hf : f ∈ 𝓜((⊤ : Opens X))) :
    Holomorphic (meromorphicToRiemannSphere f) := sorry

/-- Theorem 1.15 (2): a holomorphic map from a Riemann surface to `ℙ¹(ℂ) = OnePoint ℂ` is either
identically equal to `∞`, or else its `∞`-fiber is a discrete set and its finite part is a
meromorphic function on the complementary open subset. -/
theorem holomorphic_to_riemannSphere_eq_infty_or_meromorphic (f : X → OnePoint ℂ)
    (hf : Holomorphic f) :
    (f = fun _ ↦ (∞ : OnePoint ℂ)) ∨
      IsDiscrete (f ⁻¹' {(∞ : OnePoint ℂ)}) ∧
        MeromorphicOn (finitePartDomain f hf) (finitePart f) := sorry

end RiemannSurface
