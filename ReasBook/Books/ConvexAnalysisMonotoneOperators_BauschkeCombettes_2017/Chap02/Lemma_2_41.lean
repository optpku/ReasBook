/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u v w

open Filter
open scoped Topology

variable {H : Type u} {K : Type v}
  [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Helper for Lemma 2.41: after transporting to weak spaces, a continuous affine map splits as
its continuous linear part plus the constant translation by its value at `0`. -/
private lemma continuousAffineMap_toWeakSpace_eq_map_add_const (T : H →ᴬ[ℝ] K) :
    (fun x : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm x))) =
      fun x : WeakSpace ℝ H ↦ WeakSpace.map T.contLinear x + toWeakSpace ℝ K (T 0) := by
  -- Rewrite the transported affine map using the standard affine decomposition `T = linear + const`.
  funext x
  simpa [WeakSpace.map_apply] using
    congrFun ((T : H →ᵃ[ℝ] K).decomp) ((toWeakSpace ℝ H).symm x)

-- Proof sketch: decompose the continuous affine map `T` as its continuous linear part plus the
-- constant translation by `T 0`; the linear part is weak-to-weak continuous via `WeakSpace.map`,
-- and translation by a fixed vector is a homeomorphism for the weak topology.
/-- Lemma 2.41: a continuous affine map between real normed spaces is continuous from the weak
topology on the domain to the weak topology on the codomain. -/
theorem continuousAffineMap_continuous_toWeakSpace (T : H →ᴬ[ℝ] K) :
    Continuous fun x : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm x)) := by
  -- First rewrite the affine map as its weakly continuous linear part plus a fixed translation.
  rw [continuousAffineMap_toWeakSpace_eq_map_add_const]
  -- Then combine continuity of `WeakSpace.map T.contLinear` with continuity of addition by a constant.
  exact (WeakSpace.map T.contLinear).continuous.add continuous_const

-- Proof sketch: apply `continuousAffineMap_continuous_toWeakSpace` to the weakly convergent net
-- and use preservation of `Tendsto` under composition with a continuous map.
/-- A weakly convergent directed net remains weakly convergent after application of a continuous
affine map. -/
theorem continuousAffineMap_tendsto_toWeakSpace
    {A : Type w} [Preorder A] [IsDirectedOrder A] (T : H →ᴬ[ℝ] K) {ξ : A → H} {x : H}
    (hξ : Tendsto (fun a ↦ toWeakSpace ℝ H (ξ a)) atTop (𝓝 (toWeakSpace ℝ H x))) :
    Tendsto (fun a ↦ toWeakSpace ℝ K (T (ξ a))) atTop (𝓝 (toWeakSpace ℝ K (T x))) := by
  -- Push the weak convergence through the continuous map on weak spaces established above.
  have hT :
      Continuous fun y : WeakSpace ℝ H ↦ toWeakSpace ℝ K (T ((toWeakSpace ℝ H).symm y)) :=
    continuousAffineMap_continuous_toWeakSpace T
  exact (hT.tendsto (toWeakSpace ℝ H x)).comp hξ
