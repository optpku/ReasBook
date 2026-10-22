/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import ComputationalMethodsInverseProblems_Vogel_2002.Chap02.Definition_2_7.WellPosed
public import Mathlib.Analysis.Normed.Operator.Banach
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

public section

noncomputable section

universe u v w

/-- Companion notation for Definition 2.7: the operator equation `K f = g` is well-posed exactly
when `OperatorEquation.WellPosed K` holds, i.e. when every datum has a unique solution and the
inverse response map is continuous. The source clauses about a continuous inverse and ill-posedness
are exposed by the companion facts checked below. -/
abbrev operatorEquationWellPosed {H₁ : Type u} {H₂ : Type v}
    [TopologicalSpace H₁] [TopologicalSpace H₂] (K : H₁ → H₂) : Prop :=
  OperatorEquation.WellPosed K

#check OperatorEquation.WellPosed
#check OperatorEquation.wellPosed_iff_exists_continuousInverse
#check OperatorEquation.illPosed

namespace ContinuousLinearMap

variable {𝕜 : Type u} {H₁ : Type v} {H₂ : Type w}
variable [NontriviallyNormedField 𝕜]
variable [NormedAddCommGroup H₁] [NormedSpace 𝕜 H₁] [CompleteSpace H₁]
variable [NormedAddCommGroup H₂] [NormedSpace 𝕜 H₂] [CompleteSpace H₂]

/-- Helper for Definition 2.7: a bijective continuous linear map between Banach spaces is a
homeomorphism. -/
theorem isHomeomorph_of_bijective (K : H₁ →L[𝕜] H₂) (hK : Function.Bijective K) :
    IsHomeomorph K := by
  let e : H₁ ≃L[𝕜] H₂ := ContinuousLinearEquiv.ofBijective K
    ((LinearMap.ker_eq_bot).2 hK.1) ((LinearMap.range_eq_top).2 hK.2)
  simpa [e] using e.isHomeomorph

/-- Definition 2.7. For continuous linear operators between Banach spaces, well-posedness is
equivalent to bijectivity. -/
theorem wellPosed_iff_bijective (K : H₁ →L[𝕜] H₂) :
    OperatorEquation.WellPosed K ↔ Function.Bijective K := by
  constructor
  · -- A well-posed operator already packages injectivity and surjectivity.
    intro hK
    exact hK.bijective
  · intro hK
    -- Convert bijectivity to a homeomorphism, then invoke the general well-posedness criterion.
    exact (OperatorEquation.wellPosed_iff_isHomeomorph K.continuous).2
      (isHomeomorph_of_bijective K hK)

/-- For continuous linear operators between Banach spaces, well-posedness is equivalent to
`K.ker = ⊥` and `K.range = ⊤`. -/
theorem wellPosed_iff_ker_eq_bot_and_range_eq_top (K : H₁ →L[𝕜] H₂) :
    OperatorEquation.WellPosed K ↔ K.ker = ⊥ ∧ K.range = ⊤ := by
  constructor
  · -- Translate well-posedness to bijectivity, then rewrite injective/surjective algebraically.
    intro hK
    have hBij : Function.Bijective K := (wellPosed_iff_bijective K).1 hK
    exact ⟨(LinearMap.ker_eq_bot).2 hBij.1, (LinearMap.range_eq_top).2 hBij.2⟩
  · rintro ⟨hKer, hRange⟩
    -- The kernel/range conditions recover bijectivity, hence well-posedness.
    exact (wellPosed_iff_bijective K).2
      ⟨(LinearMap.ker_eq_bot).1 hKer, (LinearMap.range_eq_top).1 hRange⟩

variable {V : Type w}
variable [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Helper for Definition 2.7: on a finite-dimensional real normed space, a continuous linear
endomorphism is injective exactly when it is surjective. -/
theorem injective_iff_surjective (K : V →L[ℝ] V) :
    Function.Injective K ↔ Function.Surjective K := by
  -- Pass to the underlying linear endomorphism, where the finite-dimensional theorem applies.
  simpa using (LinearMap.injective_iff_surjective (f := K.toLinearMap))

/-- On a finite-dimensional real normed space, well-posedness is equivalent to injectivity. -/
theorem wellPosed_iff_injective (K : V →L[ℝ] V) :
    OperatorEquation.WellPosed K ↔ Function.Injective K := by
  -- Local instance justification (completeness): `wellPosed_iff_ker_eq_bot_and_range_eq_top`
  -- is the Banach-space theorem, and finite-dimensional real normed spaces are complete.
  haveI : CompleteSpace V := FiniteDimensional.complete ℝ V
  constructor
  · -- The kernel/range reformulation immediately yields injectivity.
    intro hK
    exact (LinearMap.ker_eq_bot).1 ((wellPosed_iff_ker_eq_bot_and_range_eq_top K).1 hK).1
  · intro hInj
    -- In finite dimension, injectivity forces surjectivity for endomorphisms.
    have hSurj : Function.Surjective K := (injective_iff_surjective K).1 hInj
    have hKer : K.ker = ⊥ := (LinearMap.ker_eq_bot).2 hInj
    have hRange : K.range = ⊤ := (LinearMap.range_eq_top).2 hSurj
    exact (wellPosed_iff_ker_eq_bot_and_range_eq_top K).2 ⟨hKer, hRange⟩

/-- On a finite-dimensional real normed space, well-posedness is equivalent to surjectivity. -/
theorem wellPosed_iff_surjective (K : V →L[ℝ] V) :
    OperatorEquation.WellPosed K ↔ Function.Surjective K := by
  -- Reuse the injective characterization and the finite-dimensional equivalence.
  rw [wellPosed_iff_injective]
  exact injective_iff_surjective K

end ContinuousLinearMap
