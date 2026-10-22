/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import RiemannSurfaces_Forster_1981.Chap01.Exercise_1_1
import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Example_1_5

open scoped Manifold OnePoint

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `onePointEquivSphereOfFinrankEq`, `stereographic'`,
  `Matrix.specialOrthogonalGroup`.
- Verified locally: `Matrix.specialOrthogonalGroup`, `onePointEquivSphereOfFinrankEq`,
  and `Matrix.mulVec`.
- Owner choice: model `ℙ¹(ℂ)` as `OnePoint ℂ`, use the canonical `Matrix.specialOrthogonalGroup`
  owner for `SO(3)`, and express biholomorphicity by `Structomorph biholomorphicGroupoid`.
-/

/-- The dimension count identifying the one-point compactification of `ℂ` with the unit sphere in
`ℝ³`. -/
private theorem complex_finrank_add_one_eq_fin3 :
    Module.finrank ℝ ℂ + 1 = Fintype.card (Fin 3) := sorry

/-- The stereographic identification of the unit sphere in `ℝ³` with the Riemann sphere
`ℙ¹(ℂ) = OnePoint ℂ`. -/
private def stereographicProjectionComplexHomeomorph :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₜ OnePoint ℂ :=
  (onePointEquivSphereOfFinrankEq complex_finrank_add_one_eq_fin3).symm

/-- A special orthogonal matrix preserves the unit sphere in `ℝ³`. -/
private theorem specialOrthogonalGroup_maps_unitSphere
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
    Matrix.toEuclideanLin A.1 x.1 ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := sorry

/-- The self-map of the Riemann sphere obtained by conjugating a rotation of `S²` by the
stereographic projection. -/
def rotationOnRiemannSphere (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    OnePoint ℂ → OnePoint ℂ :=
  fun z ↦
    let σ := stereographicProjectionComplexHomeomorph
    σ
      ⟨Matrix.toEuclideanLin A.1 (σ.symm z).1,
        specialOrthogonalGroup_maps_unitSphere A (σ.symm z)⟩

/-- The defining conjugation formula for `rotationOnRiemannSphere`. -/
theorem rotationOnRiemannSphere_def (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ)
    (z : OnePoint ℂ) :
    rotationOnRiemannSphere A z =
      let σ := stereographicProjectionComplexHomeomorph
      σ
        ⟨Matrix.toEuclideanLin A.1 (σ.symm z).1,
          specialOrthogonalGroup_maps_unitSphere A (σ.symm z)⟩ := rfl

/-- The rotation of the Riemann sphere induced by `A ∈ SO(3)` as a homeomorphism. -/
def rotationOnRiemannSphereHomeomorph (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    OnePoint ℂ ≃ₜ OnePoint ℂ where
  toEquiv :=
    { toFun := rotationOnRiemannSphere A
      invFun := rotationOnRiemannSphere A⁻¹
      left_inv := by
        sorry
      right_inv := by
        sorry }
  continuous_toFun := by
    sorry
  continuous_invFun := by
    sorry

/-- Exercise 1.3: after identifying `ℙ¹(ℂ)` with the unit sphere in `ℝ³` by stereographic
projection, every rotation `A ∈ SO(3)` induces a bundled biholomorphic self-map
`σ ∘ A ∘ σ⁻¹ : ℙ¹(ℂ) → ℙ¹(ℂ)`. -/
def rotationOnRiemannSphereStructomorph (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ) where
  toHomeomorph := rotationOnRiemannSphereHomeomorph A
  mem_groupoid := by
    sorry

@[simp] theorem rotationOnRiemannSphereStructomorph_apply
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) (z : OnePoint ℂ) :
    (rotationOnRiemannSphereStructomorph A).toHomeomorph z = rotationOnRiemannSphere A z :=
  rfl

/-- The underlying map of the induced rotation structomorphism of the Riemann sphere is
holomorphic. -/
theorem rotationOnRiemannSphere_holomorphic
    (A : Matrix.specialOrthogonalGroup (Fin 3) ℝ) :
    RiemannSurface.Holomorphic (rotationOnRiemannSphere A) := by
  simpa using
    RiemannSurface.structomorph_holomorphic (rotationOnRiemannSphereStructomorph A)
