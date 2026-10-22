/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

universe u v w

variable {𝕜 : Type w} {E₁ : Type u} {E₂ : Type v}

/-
Definition 4.4.5 lies in the normed-space operator / minimal-singular-value domain.

Sampled owner-style declarations:
- `ContinuousLinearMap.opNorm` with `ratio_le_opNorm`, the canonical mathlib owner for quotient
  norms of continuous linear maps;
- `FiniteDimensional.proper`, the compactness bridge that turns the unit sphere into a compact set
  in finite-dimensional normed spaces;
- `LinearMap.singularValues`, the stronger finite-dimensional inner-product bridge for identifying
  `σ_min(A)` with the last singular value when that extra structure is available;
- `LinearMap.singularValues_nonneg`, the canonical nonnegativity API on that stronger bridge side.

Best owner abstraction:
- source-facing: the textbook least singular value `σ_min(A)` of a continuous linear operator `A`;
- core/canonical: the infimum of the ratio `‖A x‖ / ‖x‖` over nonzero vectors;
- bridge/view: the finite-dimensional unit-sphere formula and, under stronger inner-product
  hypotheses, the identification with the last singular value.

Primitive data:
- a continuous linear operator `A : E₁ →L[𝕜] E₂`.

Derived API:
- the source-facing notation `σ_min(A)`;
- the nonnegativity theorem;
- the defining infimum formula over nonzero vectors;
- the finite-dimensional unit-sphere bridge;
- the stronger singular-value identification under inner-product hypotheses.
-/
namespace ContinuousLinearMap

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Definition 4.4.5: the least singular value of `A` is the infimum of the quotients
`‖A x‖ / ‖x‖` over nonzero vectors `x`. -/
def minimalSingularValue (A : E₁ →L[𝕜] E₂) : ℝ :=
  sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖)

end Owner

end ContinuousLinearMap

namespace MinimalSingularValue

/- Source-facing Lean notation for the textbook least singular value `σ_min(A)`. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearMap.minimalSingularValue A

end MinimalSingularValue

open scoped MinimalSingularValue

namespace ContinuousLinearEquiv

section Bridge

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Coercion bridge: the least singular value of a continuous linear equivalence, viewed through
the canonical coercion to a continuous linear map. -/
abbrev minimalSingularValue (A : E₁ ≃L[𝕜] E₂) : ℝ :=
  ContinuousLinearMap.minimalSingularValue (A : E₁ →L[𝕜] E₂)

/- Source-facing Lean notation for the textbook least singular value of a continuous linear
equivalence. -/
scoped notation:max "σ_min(" A ")" => ContinuousLinearEquiv.minimalSingularValue A

end Bridge

section NormBridge

variable [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/- Thin operator-norm bridge: a continuous linear equivalence carries the operator norm of its
underlying continuous linear map. -/
instance : Norm (E₁ ≃L[𝕜] E₂) where
  norm A := ‖(A : E₁ →L[𝕜] E₂)‖

@[simp] theorem norm_toContinuousLinearMap (A : E₁ ≃L[𝕜] E₂) :
    ‖A.toContinuousLinearMap‖ = ‖A‖ :=
  rfl

end NormBridge

end ContinuousLinearEquiv

section Owner

variable [NormedField 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Source-facing bridge: `σ_min(A)` equals the infimum of `‖A x‖ / ‖x‖` over nonzero vectors. -/
theorem minimalSingularValue_def (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) := by
  rfl

/-- The least singular value is nonnegative. -/
theorem minimalSingularValue_nonneg (A : E₁ →L[𝕜] E₂) :
    0 ≤ σ_min(A) := by
  rw [minimalSingularValue_def]
  refine Real.sInf_nonneg ?_
  rintro _ ⟨x, rfl⟩
  exact div_nonneg (norm_nonneg _) (norm_nonneg _)

/-- If the domain is subsingleton, then the least singular value is zero. -/
theorem minimalSingularValue_eq_zero [Subsingleton E₁] (A : E₁ →L[𝕜] E₂) :
    σ_min(A) = 0 := by
  rw [minimalSingularValue_def]
  have hrange :
      Set.range (fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rcases hy with ⟨x, rfl⟩
    exact x.2 <| Subsingleton.elim _ _
  simp [hrange, Real.sInf_empty]

end Owner

section UnitSphereHelpers

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Helper for Definition 4.4.5: normalizing a nonzero vector puts it on the unit sphere. -/
theorem normalize_mem_unitSphere (x : {x : E₁ // x ≠ 0}) :
    ((‖x.1‖⁻¹ : 𝕜) • x.1) ∈ Metric.sphere (0 : E₁) 1 := by
  -- The standard normalization identity gives the required unit norm directly.
  simpa [Metric.mem_sphere, dist_eq_norm] using
    (norm_smul_inv_norm (𝕜 := 𝕜) (x := x.1) x.2)

/-- Helper for Definition 4.4.5: the norm quotient at a nonzero vector is the norm of the image of
its normalization. -/
theorem norm_image_div_eq_norm_image_normalize
    (A : E₁ →L[𝕜] E₂) (x : {x : E₁ // x ≠ 0}) :
    ‖A x.1‖ / ‖x.1‖ = ‖A ((‖x.1‖⁻¹ : 𝕜) • x.1)‖ := by
  have hxnorm_pos : 0 < ‖x.1‖ := norm_pos_iff.mpr x.2
  -- Move the scalar through `A`, then simplify the resulting norm factor.
  rw [A.map_smul, norm_smul]
  simp [div_eq_mul_inv, mul_comm]

/-- Helper for Definition 4.4.5: the quotient values defining `σ_min(A)` are exactly the norms of
`A` on the unit sphere. -/
theorem minimalSingularValue_ratioRange_eq_unitSphereNormRange (A : E₁ →L[𝕜] E₂) :
    Set.range (fun x : {x : E₁ // x ≠ 0} ↦ ‖A x.1‖ / ‖x.1‖) =
      Set.range (fun x : Metric.sphere (0 : E₁) 1 ↦ ‖A x.1‖) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    -- Normalize the nonzero witness to land on the unit sphere without changing the quotient.
    refine ⟨⟨((‖x.1‖⁻¹ : 𝕜) • x.1), normalize_mem_unitSphere x⟩, ?_⟩
    simpa using (norm_image_div_eq_norm_image_normalize A x).symm
  · rintro ⟨x, rfl⟩
    refine ⟨⟨x.1, ne_zero_of_mem_sphere one_ne_zero ⟨x.1, x.property⟩⟩, ?_⟩
    -- On the unit sphere the quotient denominator is `1`, so the quotient is just `‖A x‖`.
    have hxnorm : ‖x.1‖ = 1 := by
      simp at *
    change ‖A x.1‖ / ‖x.1‖ = ‖A x.1‖
    rw [hxnorm, div_one]

/-- Helper for Definition 4.4.5: `σ_min(A)` can be read as the infimum of `‖A x‖` over the unit
sphere. -/
theorem minimalSingularValue_eq_sInf_norm_image_unitSphere_aux
    (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : Metric.sphere (0 : E₁) 1 ↦ ‖A x.1‖) := by
  -- Rewrite the defining range of quotients by the normalization bridge.
  rw [minimalSingularValue_def, minimalSingularValue_ratioRange_eq_unitSphereNormRange]

end UnitSphereHelpers

section FiniteDimensional

variable [RCLike 𝕜]
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]

/-- Over finite-dimensional normed spaces, `σ_min(A)` is the infimum of `‖A x‖` over the unit
sphere. -/
theorem minimalSingularValue_eq_sInf_norm_image_unitSphere
    (A : E₁ →L[𝕜] E₂) :
    σ_min(A) =
      sInf (Set.range fun x : Metric.sphere (0 : E₁) 1 ↦ ‖A x.1‖) := by
  -- This is exactly the earlier normalization bridge specialized to the finite-dimensional case.
  exact minimalSingularValue_eq_sInf_norm_image_unitSphere_aux A

end FiniteDimensional
