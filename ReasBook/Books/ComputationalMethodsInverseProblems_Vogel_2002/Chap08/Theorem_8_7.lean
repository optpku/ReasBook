/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Topology.OpenPartialHomeomorph.Continuity
public import ComputationalMethodsInverseProblems_Vogel_2002.Chap08.Definition_8_4.Conjugate

public section

noncomputable section

open Filter
open scoped Topology

namespace VariationalRegularization

variable {d : ℕ}

/-- Helper for Theorem 8.7: the `EReal` representation from `hrepr` becomes a
real-valued neighborhood identity after applying `EReal.toReal`. -/
lemma eventually_toReal_conjugateRepresentation
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (F :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d))
    (hrepr : ∀ᶠ y in 𝓝 (F x₀),
      conjugateFunctional C φ y =
        ((inner ℝ (F.symm y) y - φ (F.symm y) : ℝ) : EReal)) :
    ∀ᶠ y in 𝓝 (F x₀),
      (conjugateFunctional C φ y).toReal = inner ℝ (F.symm y) y - φ (F.symm y) := by
  -- Apply `EReal.toReal` to the local identity; the right-hand side is already a real coercion.
  filter_upwards [hrepr] with y hy
  rw [hy]
  simpa using (EReal.toReal_coe (inner ℝ (F.symm y) y - φ (F.symm y)))

/-- thm_8_7 (Theorem 8.7). If `x₀ ∈ C`, `φ` is differentiable near `x₀` with
local gradient map `F`, `F` has a local inverse branch near `x₀`, and near
`F x₀` the conjugate functional is attained at `F.symm y`, then near `F x₀`
the real-valued local representative of `conjugateFunctional C φ` is Fréchet
differentiable with gradient `F.symm y`. The local `EReal` representation
supplied by `hrepr` already guarantees the finiteness needed to pass to
`.toReal`. -/
theorem hasGradientAt_conjugateFunctionalToReal_of_gradient_localInverse
    (C : Set (EuclideanSpace ℝ (Fin d)))
    (φ : EuclideanSpace ℝ (Fin d) → ℝ)
    (F :
      OpenPartialHomeomorph (EuclideanSpace ℝ (Fin d)) (EuclideanSpace ℝ (Fin d)))
    (x₀ : EuclideanSpace ℝ (Fin d))
    (hx₀C : x₀ ∈ C)
    (hx₀ : x₀ ∈ F.source)
    (hφ : ∀ᶠ x in 𝓝 x₀, HasGradientAt φ (F x) x)
    (hrepr : ∀ᶠ y in 𝓝 (F x₀),
      conjugateFunctional C φ y =
        ((inner ℝ (F.symm y) y - φ (F.symm y) : ℝ) : EReal)) :
    ∀ᶠ y in 𝓝 (F x₀),
      HasGradientAt (fun y ↦ (conjugateFunctional C φ y).toReal) (F.symm y) y := by
  have hreprReal :
      ∀ᶠ y in 𝓝 (F x₀),
        (conjugateFunctional C φ y).toReal = inner ℝ (F.symm y) y - φ (F.symm y) :=
    eventually_toReal_conjugateRepresentation C φ F x₀ hrepr
  -- Route correction: differentiating the explicit representative still needs local
  -- `IsBigO` control of `F.symm`, so the source-faithful route is a sandwich proof
  -- from the supremum defining `conjugateFunctional`.
  -- That route needs the local admissibility `∀ᶠ y in 𝓝 (F x₀), F.symm y ∈ C` in order
  -- to test the supremum at `F.symm y` and `F.symm z`.
  -- The current Lean header weakens the source-side neighborhood hypothesis on `C` to
  -- the single point assumption `hx₀C : x₀ ∈ C`; the representation identity `hrepr`
  -- only identifies the value of the supremum, and does not certify that `F.symm y`
  -- itself lies in `C`.
  -- TODO: after repairing the statement with a local admissibility hypothesis for the
  -- inverse branch, prove the pointwise remainder sandwich and conclude via
  -- `hasGradientAt_iff_isLittleO`.
  sorry

end VariationalRegularization
