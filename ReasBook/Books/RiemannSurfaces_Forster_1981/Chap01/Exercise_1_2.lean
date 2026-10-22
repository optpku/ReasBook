/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import RiemannSurfaces_Forster_1981.Chap01.Definition_1_9
import RiemannSurfaces_Forster_1981.Chap01.Example_1_5
import Mathlib.Topology.Algebra.ConstMulAction
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

open scoped Manifold OnePoint

noncomputable section

/- Semantic recall:
- `lean_leansearch`: `OnePoint.map`, `UpperHalfPlane.coe_specialLinearGroup_apply`.
- Verified locally: `OnePoint.smul_some_eq_ite`, `OnePoint.smul_infty_eq_ite`,
  `RiemannSurface.Holomorphic`, `Structomorph`, and the `RiemannSurface (OnePoint ℂ)` instance.
- Owner choice: use the canonical `GL (Fin 2) ℂ` action on `OnePoint ℂ = ℙ¹(ℂ)` from
  `Mathlib.Topology.Compactification.OnePoint.ProjectiveLine` as the projective-line extension of
  the textbook linear fractional formula, and express biholomorphicity via
  `Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ)`.
-/

/-- The extension of the linear fractional transformation attached to `g ∈ GL(2, ℂ)` to the
Riemann sphere `ℙ¹(ℂ) = OnePoint ℂ`. -/
def linearFractionalExtension (g : GL (Fin 2) ℂ) : OnePoint ℂ → OnePoint ℂ :=
  fun z ↦ g • z

instance instContinuousConstSMul : ContinuousConstSMul (GL (Fin 2) ℂ) (OnePoint ℂ) where
  continuous_const_smul g := by
    sorry

/-- Exercise 1.2 (2): the extended linear fractional transformation attached to `g ∈ GL(2, ℂ)` as
a bundled biholomorphic self-equivalence of the Riemann sphere. -/
def linearFractionalStructomorph (g : GL (Fin 2) ℂ) :
    Structomorph biholomorphicGroupoid (OnePoint ℂ) (OnePoint ℂ) where
  toHomeomorph := Homeomorph.smul g
  mem_groupoid := by
    sorry

@[simp] theorem linearFractionalStructomorph_apply (g : GL (Fin 2) ℂ) (z : OnePoint ℂ) :
    (linearFractionalStructomorph g).toHomeomorph z = linearFractionalExtension g z :=
  by simp [linearFractionalStructomorph, linearFractionalExtension]

/-- On the finite chart of `ℙ¹(ℂ)`, `linearFractionalExtension g` is the usual linear fractional
formula. -/
theorem linearFractionalExtension_apply_coe (g : GL (Fin 2) ℂ) (z : ℂ) :
    linearFractionalExtension g (z : OnePoint ℂ) =
      if g 1 0 * z + g 1 1 = 0 then
        (∞ : OnePoint ℂ)
      else
        (((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) : OnePoint ℂ) := sorry

/-- At `∞`, the extended linear fractional transformation takes the expected projective value. -/
theorem linearFractionalExtension_apply_infty (g : GL (Fin 2) ℂ) :
    linearFractionalExtension g (∞ : OnePoint ℂ) =
      if g 1 0 = 0 then
        (∞ : OnePoint ℂ)
      else
        ((g 0 0 / g 1 0 : ℂ) : OnePoint ℂ) := sorry

/-- Exercise 1.2 (1): for `g ∈ GL(2, ℂ)`, the linear fractional transformation extends from the
finite chart to a holomorphic self-map of `ℙ¹(ℂ) = OnePoint ℂ`, hence to a meromorphic function on
the projective line. -/
theorem linearFractionalExtension_holomorphic (g : GL (Fin 2) ℂ) :
    RiemannSurface.Holomorphic (linearFractionalExtension g) := by
  simpa [linearFractionalExtension] using
    RiemannSurface.structomorph_holomorphic (linearFractionalStructomorph g)
