/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

universe u

variable {H : Type u}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

noncomputable section

/-- Helper for Facts 2.34 and 2.35: the inverse Riesz map from the weak dual back to `H`
equipped with the weak topology. -/
private def rieszFromWeakDual : WeakDual ℝ H → WeakSpace ℝ H :=
  fun φ ↦ toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ))

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz map from `H` with the weak topology to the
weak dual. -/
private def weakSpaceToWeakDual : WeakSpace ℝ H → WeakDual ℝ H :=
  fun x ↦ StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))

/-- Helper for Facts 2.34 and 2.35: the inverse Riesz map is continuous. -/
private theorem rieszFromWeakDual_continuous :
    Continuous (rieszFromWeakDual : WeakDual ℝ H → WeakSpace ℝ H) := by
  -- Continuity into the weak topology is checked coordinatewise against continuous linear
  -- functionals.
  refine continuous_induced_rng.2 ?_
  change Continuous (fun φ : WeakDual ℝ H ↦
    fun l : StrongDual ℝ H ↦ l ((toWeakSpace ℝ H).symm (rieszFromWeakDual φ)))
  rw [continuous_pi_iff]
  intro l
  let z : H := (InnerProductSpace.toDual ℝ H).symm l
  have hz : ∀ φ : WeakDual ℝ H,
      l ((toWeakSpace ℝ H).symm (rieszFromWeakDual φ)) = φ z := by
    intro φ
    -- The `l`-coordinate becomes evaluation of `φ` at the Riesz representer of `l`.
    simp only [rieszFromWeakDual, LinearEquiv.symm_apply_apply]
    rw [← InnerProductSpace.toDual_symm_apply]
    rw [real_inner_comm]
    rw [InnerProductSpace.toDual_symm_apply]
    simp [z]
  simpa [hz, z] using (WeakDual.eval_continuous z)

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz map is continuous from `H` with the weak
topology to the weak dual. -/
private theorem weakSpaceToWeakDual_continuous :
    Continuous (weakSpaceToWeakDual : WeakSpace ℝ H → WeakDual ℝ H) := by
  -- Continuity into the weak dual is checked coordinatewise by evaluation at vectors.
  apply WeakDual.continuous_of_continuous_eval
  intro y
  simpa [real_inner_comm, weakSpaceToWeakDual, InnerProductSpace.toDual_apply_apply] using
    (WeakBilin.eval_continuous ((topDualPairing ℝ H).flip)
      (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)))

/-- Helper for Facts 2.34, 2.35, and 2.37: composing the inverse Riesz map with the forward one
recovers the original weak vector. -/
private theorem rieszFromWeakDual_weakSpaceToWeakDual (x : WeakSpace ℝ H) :
    rieszFromWeakDual (weakSpaceToWeakDual x) = x := by
  -- This is the standard `symm_apply_apply` identity for the Riesz equivalence.
  change toWeakSpace ℝ H
      ((InnerProductSpace.toDual ℝ H).symm
        (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x))) = x
  rw [LinearIsometryEquiv.symm_apply_apply]
  exact LinearEquiv.apply_symm_apply (toWeakSpace ℝ H) x

/-- Helper for Facts 2.34, 2.35, and 2.37: composing the forward Riesz map with the inverse one
recovers the original weak dual point. -/
private theorem weakSpaceToWeakDual_rieszFromWeakDual (φ : WeakDual ℝ H) :
    weakSpaceToWeakDual (rieszFromWeakDual φ) = φ := by
  -- Equality of weak dual points is checked on all vectors.
  apply DFunLike.ext
  intro y
  simp [weakSpaceToWeakDual, rieszFromWeakDual]

/-- Helper for Facts 2.34, 2.35, and 2.37: the Riesz representation theorem identifies the weak
topology on a real Hilbert space with the weak-* topology on its dual. -/
def weakSpaceHomeomorphWeakDual : WeakSpace ℝ H ≃ₜ WeakDual ℝ H :=
  { toEquiv :=
      { toFun := weakSpaceToWeakDual
        invFun := rieszFromWeakDual
        left_inv := rieszFromWeakDual_weakSpaceToWeakDual
        right_inv := weakSpaceToWeakDual_rieszFromWeakDual }
    continuous_toFun := weakSpaceToWeakDual_continuous
    continuous_invFun := rieszFromWeakDual_continuous }

@[simp]
theorem weakSpaceHomeomorphWeakDual_apply (x : WeakSpace ℝ H) :
    weakSpaceHomeomorphWeakDual x =
      StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H ((toWeakSpace ℝ H).symm x)) :=
  rfl

@[simp]
theorem weakSpaceHomeomorphWeakDual_symm_apply (φ : WeakDual ℝ H) :
    weakSpaceHomeomorphWeakDual.symm φ =
      toWeakSpace ℝ H ((InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ)) :=
  rfl

private lemma rieszFromWeakDual_image_closedBall :
    rieszFromWeakDual ''
        (WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1) =
      ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) 1 : Set (WeakSpace ℝ H)) := by
  ext x
  constructor
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨(InnerProductSpace.toDual ℝ H).symm (WeakDual.toStrongDual φ), ?_, ?_⟩
    · -- The inverse Riesz map preserves norms, so membership in the dual closed ball transports
      -- to membership in the Hilbert-space closed ball.
      simpa [Metric.mem_closedBall, dist_eq_norm, ((InnerProductSpace.toDual ℝ H).symm).norm_map]
        using hφ
    · simp [rieszFromWeakDual]
  · rintro ⟨y, hy, rfl⟩
    refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y), ?_, ?_⟩
    · -- The forward Riesz map is also an isometry, so vectors in the Hilbert-space unit ball map
      -- into the dual closed unit ball.
      have hy' : ‖InnerProductSpace.toDual ℝ H y‖ ≤ 1 := by
        simpa [(InnerProductSpace.toDual ℝ H).norm_map, Metric.mem_closedBall, dist_eq_norm]
          using hy
      change WeakDual.toStrongDual (StrongDual.toWeakDual (InnerProductSpace.toDual ℝ H y)) ∈
        Metric.closedBall (0 : StrongDual ℝ H) 1
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
      change ‖InnerProductSpace.toDual ℝ H y‖ ≤ 1
      exact hy'
    · change (InnerProductSpace.toDual ℝ H).symm ((InnerProductSpace.toDual ℝ H) y) = y
      simp

/-- Fact 2.34: the closed unit ball of a real Hilbert space is compact for the weak topology.
This is the Banach--Alaoglu--Bourbaki compactness statement in the Hilbert-space setting. -/
-- Proof sketch: transport the weak topology on `H` to the weak-* topology on the continuous dual
-- via the Fréchet-Riesz isometric equivalence `InnerProductSpace.toDual ℝ H`, identify the image of
-- the unit ball with the weak-* closed unit ball in the dual, and apply
-- `WeakDual.isCompact_closedBall`.
theorem isCompact_unitBall_weakSpace :
    IsCompact ((toWeakSpace ℝ H) '' Metric.closedBall (0 : H) 1 : Set (WeakSpace ℝ H)) := by
  let dualBall : Set (WeakDual ℝ H) :=
    WeakDual.toStrongDual ⁻¹' Metric.closedBall (0 : StrongDual ℝ H) 1
  -- Banach-Alaoglu gives weak-* compactness of the dual closed unit ball.
  have hcompact : IsCompact dualBall :=
    WeakDual.isCompact_closedBall (0 : StrongDual ℝ H) 1
  -- The inverse Riesz map sends that compact set onto the weak unit ball in `H`.
  have himage : IsCompact (rieszFromWeakDual '' dualBall) :=
    hcompact.image rieszFromWeakDual_continuous
  convert himage using 1
  symm
  exact rieszFromWeakDual_image_closedBall
