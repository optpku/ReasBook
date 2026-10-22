/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.LocallyConvex.SeparatingDual
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual

public section

universe u

open scoped InnerProductSpace

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- A sequence `f : ℕ → H` converges weakly to `fStar` if it converges to `fStar` in
`WeakSpace ℝ H`. -/
def weakSeqTendsto (f : ℕ → H) (fStar : H) : Prop :=
  Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (f n)) Filter.atTop
    (nhds (toWeakSpace ℝ H fStar))

/-- Rewrites `weakSeqTendsto` as ordinary convergence in `WeakSpace ℝ H`. -/
theorem weakSeqTendsto_iff {f : ℕ → H} {fStar : H} :
    weakSeqTendsto f fStar ↔
      Filter.Tendsto (fun n ↦ toWeakSpace ℝ H (f n)) Filter.atTop
        (nhds (toWeakSpace ℝ H fStar)) := by
  -- This theorem is just the defining reformulation of `weakSeqTendsto`.
  rfl

/-- Helper for Definition 2.22: evaluating a continuous linear functional on `toWeakSpace ℝ H x`
is the same as evaluating it on `x`. -/
lemma dual_apply_toWeakSpace (ℓ : StrongDual ℝ H) (x : H) :
    ℓ (toWeakSpace ℝ H x) = ℓ x := rfl

/-- Rewrites `weakSeqTendsto` by testing against all continuous linear functionals on `H`. -/
theorem weakSeqTendsto_iff_forall_dual_apply_tendsto {f : ℕ → H} {fStar : H} :
    weakSeqTendsto f fStar ↔
      ∀ ℓ : StrongDual ℝ H, Filter.Tendsto (fun n ↦ ℓ (f n)) Filter.atTop (nhds (ℓ fStar)) :=
  by
  -- First normalize weak convergence to convergence in the weak topology.
  rw [weakSeqTendsto_iff]
  -- Then characterize convergence in `WeakSpace ℝ H` by convergence of all evaluations.
  have hPairingInjective : Function.Injective ((topDualPairing ℝ H).flip) := by
    intro x y hxy
    by_contra hne
    obtain ⟨ℓ, hℓ⟩ :=
      (inferInstance : SeparatingDual ℝ H).exists_ne_zero' (x - y) (sub_ne_zero_of_ne hne)
    have hxy' : ℓ x = ℓ y := DFunLike.congr_fun hxy ℓ
    have hSub : ℓ (x - y) = 0 := by
      simpa [map_sub] using sub_eq_zero.mpr hxy'
    exact hℓ hSub
  constructor
  · intro h ℓ
    -- Apply the weak-topology characterization and evaluate at the chosen functional.
    exact
      (by
        have hEval :=
          (WeakBilin.tendsto_iff_forall_eval_tendsto
            (B := (topDualPairing ℝ H).flip)
            (l := Filter.atTop)
            (f := fun n ↦ toWeakSpace ℝ H (f n))
            (x := toWeakSpace ℝ H fStar)
            hPairingInjective).1 h ℓ
        simpa [topDualPairing_apply, dual_apply_toWeakSpace] using hEval)
  · intro h
    -- Conversely, the assumed scalar convergence closes the weak-topology criterion.
    refine
      (WeakBilin.tendsto_iff_forall_eval_tendsto
        (B := (topDualPairing ℝ H).flip)
        (l := Filter.atTop)
        (f := fun n ↦ toWeakSpace ℝ H (f n))
        (x := toWeakSpace ℝ H fStar)
        hPairingInjective).2 ?_
    intro ℓ
    simpa [topDualPairing_apply, dual_apply_toWeakSpace] using h ℓ

variable [CompleteSpace H]

/-- Helper for Definition 2.22: the dual-functional formulation of weak sequential convergence is
equivalent to the inner-product formulation given by the Riesz map. -/
lemma forallDualApplyTendsto_iff_forallInnerTendsto {f : ℕ → H} {fStar : H} :
    (∀ ℓ : StrongDual ℝ H, Filter.Tendsto (fun n ↦ ℓ (f n)) Filter.atTop (nhds (ℓ fStar))) ↔
      ∀ g : H,
        Filter.Tendsto (fun n ↦ ⟪f n, g⟫_ℝ) Filter.atTop (nhds (⟪fStar, g⟫_ℝ)) := by
  constructor
  · intro h g
    -- Evaluate the dual criterion on the Riesz functional corresponding to `g`.
    simpa [real_inner_comm] using h (InnerProductSpace.toDual ℝ H g)
  · intro h ℓ
    -- Rewrite an arbitrary functional through its Riesz representative.
    have hInner := h ((InnerProductSpace.toDual ℝ H).symm ℓ)
    have hEval :
        (fun n ↦ ⟪f n, (InnerProductSpace.toDual ℝ H).symm ℓ⟫_ℝ) = fun n ↦ ℓ (f n) := by
      ext n
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    have hLimit : ⟪fStar, (InnerProductSpace.toDual ℝ H).symm ℓ⟫_ℝ = ℓ fStar := by
      rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
    simpa [hEval, hLimit] using hInner

/-- Definition 2.22. A sequence `f : ℕ → H` converges weakly to `fStar` if and only if
`⟪f n - fStar, g⟫_ℝ → 0` for every `g : H`. -/
theorem weakSeqTendsto_iff_forall_inner_tendsto_zero {f : ℕ → H} {fStar : H} :
    weakSeqTendsto f fStar ↔
      ∀ g : H, Filter.Tendsto (fun n ↦ ⟪f n - fStar, g⟫_ℝ) Filter.atTop (nhds 0) := by
  -- Route correction: prove the textbook criterion from the canonical dual formulation first.
  rw [weakSeqTendsto_iff_forall_dual_apply_tendsto, forallDualApplyTendsto_iff_forallInnerTendsto]
  constructor
  · intro h g
    -- Convert convergence to `⟪fStar, g⟫` into convergence of the centered inner products to `0`.
    simpa [inner_sub_left] using (tendsto_sub_nhds_zero_iff.2 (h g))
  · intro h g
    -- Recover convergence of `⟪f n, g⟫` from the centered convergence statement.
    exact tendsto_sub_nhds_zero_iff.1 (by simpa [inner_sub_left] using h g)

/-- Rewrites weak sequential convergence in terms of pointwise convergence of the inner products
`⟪f n, g⟫_ℝ` to `⟪fStar, g⟫_ℝ`. -/
theorem weakSeqTendsto_iff_forall_inner_tendsto {f : ℕ → H} {fStar : H} :
    weakSeqTendsto f fStar ↔
      ∀ g : H,
        Filter.Tendsto (fun n ↦ ⟪f n, g⟫_ℝ) Filter.atTop (nhds (⟪fStar, g⟫_ℝ)) := by
  rw [weakSeqTendsto_iff_forall_inner_tendsto_zero]
  constructor
  · intro h g
    -- The zero-limit formulation is equivalent to convergence to the target value.
    exact tendsto_sub_nhds_zero_iff.1 (by simpa [inner_sub_left] using h g)
  · intro h g
    -- Center the convergent scalar sequence around its limit.
    simpa [inner_sub_left] using (tendsto_sub_nhds_zero_iff.2 (h g))
