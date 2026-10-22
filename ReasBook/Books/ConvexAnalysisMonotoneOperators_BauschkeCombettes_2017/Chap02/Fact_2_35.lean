/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Fact_2_34

-- Declarations for this item will be appended below by the statement pipeline.

open TopologicalSpace
open scoped InnerProductSpace

universe u

noncomputable section

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The closed unit ball of a real Hilbert space, viewed with the weak subspace topology. -/
abbrev weakClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H] :=
  {x : WeakSpace ℝ H // ‖(toWeakSpace ℝ H).symm x‖ ≤ 1}

/-- Every point of `weakClosedUnitBall H` has underlying norm at most `1`. -/
theorem weakClosedUnitBall_norm_le_one (x : weakClosedUnitBall H) :
    ‖(toWeakSpace ℝ H).symm x‖ ≤ 1 := by
  -- The closed-ball inequality is exactly the subtype predicate.
  exact x.2

/-- Helper for Fact 2.35: the normalized vector `x / ‖x‖` belongs to the weak closed unit ball
whenever `x ≠ 0`. -/
private theorem normalized_mem_weakClosedUnitBall (x : H) (hx : x ≠ 0) :
    ‖(‖x‖)⁻¹ • x‖ ≤ 1 := by
  -- Normalization places the vector on the unit sphere.
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg x))]
  exact le_of_eq (inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx))

/-- Helper for Fact 2.35: the normalized nonzero vector as a point of the weak closed unit ball. -/
private def normalizedWeakClosedUnitBall (x : H) (hx : x ≠ 0) :
    weakClosedUnitBall H :=
  ⟨toWeakSpace ℝ H ((‖x‖)⁻¹ • x), normalized_mem_weakClosedUnitBall x hx⟩

section Complete

variable [CompleteSpace H]

/-- Helper for Fact 2.35: the weak-* closed unit ball in the continuous dual of `H`. -/
private abbrev weakDualClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :=
  {φ : WeakDual ℝ H // WeakDual.toStrongDual φ ∈ Metric.closedBall (0 : StrongDual ℝ H) 1}

/-- Helper for Fact 2.35: the Fréchet-Riesz map sends the weak closed unit ball of `H` into the
weak-* closed unit ball of the dual. -/
private theorem weakClosedUnitBall_toWeakDual_mem (x : weakClosedUnitBall H) :
    WeakDual.toStrongDual
        (weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H)) ∈
      Metric.closedBall (0 : StrongDual ℝ H) 1 := by
  -- The Riesz map is an isometry, so the norm bound is transported unchanged.
  have hx : ‖WeakDual.toStrongDual
      (weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H))‖ ≤ 1 := by
    change ‖InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x)‖ ≤ 1
    rw [(InnerProductSpace.toDual ℝ H).norm_map]
    exact weakClosedUnitBall_norm_le_one x
  simpa [Metric.mem_closedBall, dist_eq_norm] using hx

/-- Helper for Fact 2.35: the inverse Riesz map sends the weak-* dual closed unit ball back to the
weak closed unit ball of `H`. -/
private theorem weakDualClosedUnitBall_toWeakClosedUnitBall_mem (φ : weakDualClosedUnitBall H) :
    ‖(toWeakSpace ℝ H).symm (weakSpaceHomeomorphWeakDual.symm (φ : WeakDual ℝ H))‖ ≤ 1 := by
  -- Again, the inverse Riesz map preserves the norm.
  have hφ : ‖WeakDual.toStrongDual (φ : WeakDual ℝ H)‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm] using φ.2
  change ‖(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual (φ : WeakDual ℝ H))‖ ≤ 1
  rw [((InnerProductSpace.toDual ℝ H).symm).norm_map]
  exact hφ

/-- Helper for Fact 2.35: weak inner-product coordinates are continuous on `H` equipped with the
weak topology. -/
theorem weakSpace_continuous_inner_right (y : H) :
    Continuous fun x : WeakSpace ℝ H ↦ inner ℝ ((toWeakSpace ℝ H).symm x) y := by
  -- Coordinate maps in the weak topology are continuous by definition, and in the Hilbert-space
  -- setting the Riesz map identifies them with inner products against fixed vectors.
  simpa [real_inner_comm, InnerProductSpace.toDual_apply_apply] using
    (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (weakSpaceHomeomorphWeakDual (toWeakSpace ℝ H y)))

/-- Helper for Fact 2.35: the forward Riesz map restricted to the weak closed unit ball. -/
private def weakClosedUnitBallToWeakDualClosedUnitBall :
    weakClosedUnitBall H → weakDualClosedUnitBall H :=
  fun x ↦ ⟨weakSpaceHomeomorphWeakDual (x : WeakSpace ℝ H), weakClosedUnitBall_toWeakDual_mem x⟩

/-- Helper for Fact 2.35: the inverse Riesz map restricted to the weak-* dual closed unit ball. -/
private def weakDualClosedUnitBallToWeakClosedUnitBall :
    weakDualClosedUnitBall H → weakClosedUnitBall H :=
  fun φ ↦
    ⟨weakSpaceHomeomorphWeakDual.symm (φ : WeakDual ℝ H),
      weakDualClosedUnitBall_toWeakClosedUnitBall_mem φ⟩

/-- Helper for Fact 2.35: the restricted forward Riesz map is continuous. -/
private theorem weakClosedUnitBallToWeakDualClosedUnitBall_continuous :
    Continuous (weakClosedUnitBallToWeakDualClosedUnitBall :
      weakClosedUnitBall H → weakDualClosedUnitBall H) := by
  -- We just compose the continuous whole-space map with the subtype inclusion.
  apply Continuous.subtype_mk
  exact weakSpaceHomeomorphWeakDual.continuous.comp continuous_subtype_val

/-- Helper for Fact 2.35: the restricted inverse Riesz map is continuous. -/
private theorem weakDualClosedUnitBallToWeakClosedUnitBall_continuous :
    Continuous (weakDualClosedUnitBallToWeakClosedUnitBall :
      weakDualClosedUnitBall H → weakClosedUnitBall H) := by
  -- The same argument works for the inverse map.
  apply Continuous.subtype_mk
  exact weakSpaceHomeomorphWeakDual.symm.continuous.comp continuous_subtype_val

/-- Helper for Fact 2.35: the restricted inverse Riesz map is a left inverse to the restricted
forward map. -/
private theorem weakDualClosedUnitBall_left_inv (x : weakClosedUnitBall H) :
    weakDualClosedUnitBallToWeakClosedUnitBall
        (weakClosedUnitBallToWeakDualClosedUnitBall x) = x := by
  -- Equality of subtype points reduces to equality of their ambient weak vectors.
  apply Subtype.ext
  exact weakSpaceHomeomorphWeakDual.left_inv (x : WeakSpace ℝ H)

/-- Helper for Fact 2.35: the restricted forward Riesz map is a right inverse to the restricted
inverse map. -/
private theorem weakClosedUnitBall_right_inv (φ : weakDualClosedUnitBall H) :
    weakClosedUnitBallToWeakDualClosedUnitBall
        (weakDualClosedUnitBallToWeakClosedUnitBall φ) = φ := by
  -- Again, equality is checked on the ambient weak-* functionals.
  apply Subtype.ext
  exact weakSpaceHomeomorphWeakDual.right_inv (φ : WeakDual ℝ H)

/-- Helper for Fact 2.35: the weak closed unit ball of `H` is homeomorphic to the weak-* closed
unit ball of the dual via the Riesz representation theorem. -/
private def weakClosedUnitBall_homeomorph_weakDual_closedBall :
    weakClosedUnitBall H ≃ₜ weakDualClosedUnitBall H :=
  { toEquiv :=
      { toFun := weakClosedUnitBallToWeakDualClosedUnitBall
        invFun := weakDualClosedUnitBallToWeakClosedUnitBall
        left_inv := weakDualClosedUnitBall_left_inv
        right_inv := weakClosedUnitBall_right_inv }
    continuous_toFun := weakClosedUnitBallToWeakDualClosedUnitBall_continuous
    continuous_invFun := weakDualClosedUnitBallToWeakClosedUnitBall_continuous }

private instance : CompactSpace (weakDualClosedUnitBall H) := by
  let K : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
  have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
  simpa [weakDualClosedUnitBall, K, isCompact_iff_compactSpace] using
    (isCompact_iff_compactSpace.mp hK)

/-- Helper for Fact 2.35: the weak closed unit ball is a compact space. -/
instance : CompactSpace (weakClosedUnitBall H) :=
  weakClosedUnitBall_homeomorph_weakDual_closedBall.symm.compactSpace

/-- Helper for Fact 2.35: the evaluation map sending `x` to the weak-coordinate function
`u ↦ ⟪u, x⟫` on the weak closed unit ball. -/
def evalOnWeakClosedUnitBall (H : Type u) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] :
    H → C(weakClosedUnitBall H, ℝ) :=
  fun x ↦
    { toFun := fun u ↦ inner ℝ ((toWeakSpace ℝ H).symm u) x
      continuous_toFun := (weakSpace_continuous_inner_right x).comp continuous_subtype_val }

/-- Helper for Fact 2.35: the evaluation map is additive, hence it respects subtraction. -/
private theorem evalOnWeakClosedUnitBall_sub (x y : H) :
    evalOnWeakClosedUnitBall H (x - y) =
      evalOnWeakClosedUnitBall H x - evalOnWeakClosedUnitBall H y := by
  -- Pointwise subtraction is just linearity of the inner product in the second slot.
  ext u
  simp [evalOnWeakClosedUnitBall, inner_sub_right]

/-- Helper for Fact 2.35: the evaluation map has norm exactly `‖x‖`. -/
theorem evalOnWeakClosedUnitBall_norm_eq (x : H) :
    ‖evalOnWeakClosedUnitBall H x‖ = ‖x‖ := by
  -- The upper bound comes from Cauchy-Schwarz and the unit-ball constraint.
  have hub : ‖evalOnWeakClosedUnitBall H x‖ ≤ ‖x‖ := by
    rw [ContinuousMap.norm_le (evalOnWeakClosedUnitBall H x) (norm_nonneg x)]
    intro u
    have hu : ‖(toWeakSpace ℝ H).symm u‖ * ‖x‖ ≤ 1 * ‖x‖ := by
      exact mul_le_mul_of_nonneg_right (weakClosedUnitBall_norm_le_one u) (norm_nonneg x)
    calc
      ‖evalOnWeakClosedUnitBall H x u‖
          = |inner ℝ ((toWeakSpace ℝ H).symm u) x| := rfl
      _ ≤ ‖(toWeakSpace ℝ H).symm u‖ * ‖x‖ := abs_real_inner_le_norm _ _
      _ ≤ 1 * ‖x‖ := hu
      _ = ‖x‖ := by ring
  by_cases hx : x = 0
  · -- At the zero vector the norm identity is immediate.
    subst hx
    have hzero : evalOnWeakClosedUnitBall H (0 : H) = 0 := by
      ext u
      simp [evalOnWeakClosedUnitBall]
    rw [hzero]
    simp
  · -- Route correction: for the lower bound we test the function at the normalized vector
    -- `x / ‖x‖`, which lies in the weak closed unit ball.
    let u : weakClosedUnitBall H := normalizedWeakClosedUnitBall x hx
    have hu_eval : evalOnWeakClosedUnitBall H x u = ‖x‖ := by
      -- Evaluating at the normalized vector achieves the operator norm exactly.
      change inner ℝ ((‖x‖)⁻¹ • x) x = ‖x‖
      rw [real_inner_smul_left, real_inner_self_eq_norm_sq]
      field_simp [norm_ne_zero_iff.mpr hx]
    have hlow : ‖x‖ ≤ ‖evalOnWeakClosedUnitBall H x‖ := by
      simpa [hu_eval] using ContinuousMap.norm_coe_le_norm (evalOnWeakClosedUnitBall H x) u
    exact le_antisymm hub hlow

/-- Helper for Fact 2.35: the evaluation embedding of `H` into continuous functions on the weak
closed unit ball is an isometry. -/
private theorem evalOnWeakClosedUnitBall_isometry : Isometry (evalOnWeakClosedUnitBall H) := by
  -- Distances are computed by the norm of the difference, and the previous norm formula applies
  -- to that difference.
  refine Isometry.of_dist_eq fun x y ↦ ?_
  rw [dist_eq_norm, dist_eq_norm]
  calc
    ‖evalOnWeakClosedUnitBall H x - evalOnWeakClosedUnitBall H y‖
        = ‖evalOnWeakClosedUnitBall H (x - y)‖ := by
            rw [← evalOnWeakClosedUnitBall_sub]
    _ = ‖x - y‖ := evalOnWeakClosedUnitBall_norm_eq (x - y)

/-- Fact 2.35: the weak topology on the closed unit ball of a real Hilbert space is metrizable if
and only if the Hilbert space is separable. -/
theorem weakClosedUnitBall_metrizable_iff_separable :
    MetrizableSpace (weakClosedUnitBall H) ↔ SeparableSpace H := by
  constructor
  · intro hmetr
    -- Compactness plus metrizability makes the weak closed unit ball second countable, so the
    -- evaluation isometry embeds `H` into the separable space `C(K, ℝ)`.
    letI : MetrizableSpace (weakClosedUnitBall H) := hmetr
    haveI : SecondCountableTopology (weakClosedUnitBall H) := by infer_instance
    haveI : SecondCountableTopology C(weakClosedUnitBall H, ℝ) := by infer_instance
    exact evalOnWeakClosedUnitBall_isometry.isEmbedding.separableSpace
  · intro hsep
    -- The weak ball is homeomorphic to a weak-* compact dual ball, and the latter is metrizable
    -- in the separable case by the countable-separating theorem from mathlib.
    letI : SeparableSpace H := hsep
    let K : Set (WeakDual ℝ H) :=
      WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
    have hK : IsCompact K := WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
    haveI : MetrizableSpace (weakDualClosedUnitBall H) := by
      simpa [weakDualClosedUnitBall, K] using
        (WeakDual.metrizable_of_isCompact ℝ H K hK)
    exact weakClosedUnitBall_homeomorph_weakDual_closedBall.isEmbedding.metrizableSpace

end Complete
