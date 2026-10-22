/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap19.Proposition_19_25

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped InnerProductSpace

universe u v

namespace ERealFunction

section ParametricDuality

variable {H : Type u} {G : Type v}
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]

private theorem zero_mem_polarCone (K : Set G) :
    (0 : G) ∈ Set.polarCone K := by
  rw [Set.mem_polarCone_iff_forall_inner_nonpos]
  intro y hy
  simp

-- Proof sketch: use the saddle-point inequality directly on the canonical owner
-- `ℒ[inequalityConstraintPerturbation f R K]`. Proposition 19.25(4) identifies each Lagrangian
-- fiber under the cone hypotheses. At `(x̄, v̄)`, the saddle-point condition forces the polar-cone
-- branch, so the Lagrangian value is exactly `f x̄ + ⟪R x̄, v̄⟫`; for arbitrary `x`, the same
-- formula gives an upper bound by `f x + ⟪R x, v̄⟫`.
/-- Remark 19.26: if `(x̄, v̄)` is a saddle point of the Lagrangian attached to the inequality-
constraint perturbation, then the associated multiplier `v̄` makes `x̄` solve the unconstrained
minimization problem `min_x f x + ⟪R x, v̄⟫`. -/
theorem mem_argmin_of_isInequalityConstraintLagrangeMultiplier
    (f : H → Set.Ioi (⊥ : EReal))
    (R : H → G) (K : Set G)
    (hK_nonempty : K.Nonempty) (hK_cone : IsCone K)
    {xbar : H} {vbar : G}
    (hsaddle :
      IsSaddlePointOn (Set.univ : Set H) (Set.univ : Set G)
        (ℒ[inequalityConstraintPerturbation f R K]) xbar vbar) :
    xbar ∈ Argmin (fun x : H ↦ (f x : EReal) + (⟪R x, vbar⟫_ℝ : EReal)) := by
  rw [mem_argmin_iff, isMinOn_univ_iff]
  intro x
  let F := inequalityConstraintPerturbation f R K
  let φ : H → EReal := fun z ↦ (f z : EReal) + (⟪R z, vbar⟫_ℝ : EReal)
  have hzero_polar : (0 : G) ∈ Set.polarCone K :=
    zero_mem_polarCone K
  by_cases hxbar : xbar ∈ effectiveDomain f
  · have hvbar : vbar ∈ Set.polarCone K := by
      have hle : ℒ[F] xbar 0 ≤ ℒ[F] xbar vbar :=
        hsaddle xbar (by simp) 0 (by simp)
      by_cases hvbar : vbar ∈ Set.polarCone K
      · exact hvbar
      · rw [lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone xbar 0,
          lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone xbar vbar] at hle
        have hbot : (f xbar : EReal) = ⊥ := by
          simpa [hxbar, hzero_polar, hvbar] using hle
        exact False.elim <| (ne_of_gt (f xbar).2) hbot
    have hxbar_eq :
        ℒ[F] xbar vbar = φ xbar := by
      rw [lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone xbar vbar]
      simp [φ, hxbar, hvbar]
    have hx_le : ℒ[F] x vbar ≤ φ x := by
      rw [lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone x vbar]
      by_cases hx : x ∈ effectiveDomain f
      · by_cases hvx : vbar ∈ Set.polarCone K
        · simp [φ, hx, hvx]
        · simp [φ, hx, hvx]
      · have hfx_top : (f x : EReal) = ⊤ := by
          exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hx))
        simp [φ, hx, hfx_top]
    calc
      φ xbar = ℒ[F] xbar vbar := hxbar_eq.symm
      _ ≤ ℒ[F] x vbar := hsaddle x (by simp) vbar (by simp)
      _ ≤ φ x := hx_le
  · have hfxbar_top : (f xbar : EReal) = ⊤ := by
      exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hxbar))
    have hlag_top : ℒ[F] xbar vbar = ⊤ := by
      rw [lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone xbar vbar]
      simp [hxbar]
    have hlag_zero_top : ℒ[F] xbar 0 = ⊤ := by
      rw [lagrangian_inequalityConstraintPerturbation f R K hK_nonempty hK_cone xbar 0]
      simp [hxbar]
    have hall_top : ∀ z : H, (f z : EReal) = ⊤ := by
      intro z
      by_cases hz : z ∈ effectiveDomain f
      · by_cases hvbar : vbar ∈ Set.polarCone K
        · have hle : ℒ[F] xbar vbar ≤ ℒ[F] z vbar :=
            hsaddle z (by simp) vbar (by simp)
          rw [hlag_top, lagrangian_inequalityConstraintPerturbation
              f R K hK_nonempty hK_cone z vbar] at hle
          have htop : (f z : EReal) + (⟪R z, vbar⟫_ℝ : EReal) = ⊤ := by
            simpa [hz, hvbar] using hle
          have hfz_top : (f z : EReal) ≠ ⊤ :=
            ne_of_lt (mem_effectiveDomain_iff.mp hz)
          exact False.elim <| EReal.add_ne_top hfz_top (EReal.coe_ne_top _) htop
        · have hle : ℒ[F] xbar 0 ≤ ℒ[F] z vbar :=
            hsaddle z (by simp) 0 (by simp)
          rw [hlag_zero_top, lagrangian_inequalityConstraintPerturbation
              f R K hK_nonempty hK_cone z vbar] at hle
          simp [hz, hvbar] at hle
      · exact le_antisymm le_top (not_lt.mp (by simpa [mem_effectiveDomain_iff] using hz))
    have hφ_top : ∀ z : H, φ z = ⊤ := by
      intro z
      simp [φ, hall_top z]
    simpa [φ, hφ_top xbar]
      using (show (⊤ : EReal) ≤ φ x from by rw [hφ_top x])

end ParametricDuality

end ERealFunction
