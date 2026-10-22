/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap05.Definition_5_4_4_1

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open Metric
open scoped Matrix.Norms.L2Operator RealSymmetricMatrixSpace

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℝ

/- Definition 6.49 lies in the operator-norm / symmetric-matrix spectral-norm domain.

Primary domain:
- operator norms of continuous linear maps into the real symmetric-matrix space `𝕊^n`;
- the ambient matrix spectral norm in the scoped `Matrix.Norms.L2Operator` owner.

Sampled owner-style declarations:
- mathlib `ContinuousLinearMap.opNorm`;
- mathlib `ContinuousLinearMap.sSup_sphere_eq_norm`;
- Chapter 5 `𝕊^n`.

Best owner abstraction:
- source-facing: the operator norm of `A : E →L[ℝ] 𝕊^n`, where `E` models the chosen normed
  structure on `ℝ^m`;
- core/canonical: the ambient norm `‖A‖`;
- bridge/view: the unit-sphere spectral-norm formula and, in finite dimensions, existence of a
  maximizing unit vector.

Primitive data:
- a real normed space `E`;
- a continuous linear map `A : E →L[ℝ] 𝕊^n`.

Derived API:
- the canonical operator norm `‖A‖`;
- the source-facing sphere formula in terms of the ambient matrix spectral norm;
- the finite-dimensional attainment statement recovering the textbook maximum.

Source/core/bridge triage:
- source-facing: Definition 6.49 as the operator norm induced by the source norm and the spectral
  norm on symmetric matrices;
- core/canonical: `ContinuousLinearMap.opNorm`;
- bridge/view: the symmetric-matrix-to-matrix coercion inside the sphere formula.
-/

/- The canonical owner note for this item: the operator norm induced by the chosen norm on the
source and the spectral norm on `S_n` is the canonical norm on `E →L[ℝ] 𝕊^n`. -/

-- Proof sketch: specialize `ContinuousLinearMap.sSup_sphere_eq_norm` to the symmetric-matrix
-- codomain.
/-- Helper for Definition 6.49: the canonical operator norm of a symmetric-matrix-valued map is
the supremum of `‖A h‖` over the unit sphere of the source space. -/
theorem operatorNorm_eq_sSup_unitSphere (A : E →L[ℝ] 𝕊^n) :
    ‖A‖ = sSup ((fun h : E ↦ ‖A h‖) '' sphere (0 : E) 1) := by
  -- The canonical operator norm is already the sphere supremum in mathlib.
  simpa using A.sSup_sphere_eq_norm.symm

-- Proof sketch: the unit sphere of a finite-dimensional real normed space is compact, the map
-- `h ↦ ‖((A h : 𝕊^n) : Mat)‖` is continuous, and
-- `operatorNorm_eq_sSup_unitSphere` identifies `‖A‖` with the resulting maximum.
/-- Definition 6.49: in finite dimensions, the operator norm of `A` is attained at some unit
vector of the source space. For the source-faithful maximum formulation, the source space must be
nontrivial so that the unit sphere is nonempty. This recovers the textbook maximum formulation. -/
theorem operatorNorm_exists_unitSphere_spectralNorm_maximizer
    [FiniteDimensional ℝ E] [Nontrivial E] (A : E →L[ℝ] 𝕊^n) :
    ∃ h ∈ sphere (0 : E) 1, ‖A‖ = ‖((A h : 𝕊^n) : Mat)‖ := by
  -- The operator norm of a continuous linear map is a continuous real-valued function on the
  -- source sphere.
  have hcont : ContinuousOn (fun h : E ↦ ‖A h‖) (sphere (0 : E) 1) :=
    A.continuous.norm.continuousOn
  -- Compactness and nonemptiness of the unit sphere produce a point whose value is the sphere
  -- supremum.
  obtain ⟨h, hh, hsSup⟩ := (isCompact_sphere (0 : E) 1).exists_sSup_image_eq
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont
  refine ⟨h, hh, ?_⟩
  -- Rewrite the operator norm as the sphere supremum and evaluate that supremum at the
  -- maximizing point.
  calc
    ‖A‖ = sSup ((fun x : E ↦ ‖A x‖) '' sphere (0 : E) 1) := by
      simpa using operatorNorm_eq_sSup_unitSphere (E := E) (n := n) A
    _ = ‖A h‖ := hsSup
    _ = ‖((A h : 𝕊^n) : Mat)‖ := by
      simp

end

end
