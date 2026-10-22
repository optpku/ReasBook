/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u v w z

namespace LinearMap

variable {A : Type z} [Preorder A]
variable {H : Type u} {G : Type v} {K : Type w}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup G] [InnerProductSpace ℝ G]
variable [NormedAddCommGroup K] [InnerProductSpace ℝ K]

/-- Lemma 2.43: a bilinear map between real Hilbert spaces that satisfies a global norm bound sends
a bounded strongly convergent net in the first variable and a strongly convergent net in the second
variable to a strongly convergent net. -/
-- Proof sketch: the norm bound upgrades `T` to a continuous bilinear map. Joint continuity then
-- gives the convergence of `a ↦ T (x_net a) (u_net a)` directly, so the boundedness assumption on
-- `x_net` is retained only to match the textbook statement.
theorem tendsto_apply_bilinear_of_tendsto_of_bounded_range
    (T : H →ₗ[ℝ] G →ₗ[ℝ] K)
    (hT : ∃ beta : ℝ, 0 < beta ∧ ∀ x u, ‖T x u‖ ≤ beta * ‖x‖ * ‖u‖)
    {x_net : A → H} {u_net : A → G} {x : H} {u : G}
    (_hx_bdd : Bornology.IsBounded (Set.range x_net))
    (hx : Tendsto x_net atTop (nhds x))
    (hu : Tendsto u_net atTop (nhds u)) :
    Tendsto (fun a ↦ T (x_net a) (u_net a)) atTop (nhds (T x u)) := by
  obtain ⟨beta, hbeta_pos, hbeta⟩ := hT
  simpa [LinearMap.mkContinuous₂_apply] using
    ((T.mkContinuous₂ beta hbeta).continuous₂.tendsto (x, u)).comp (hx.prodMk_nhds hu)

end LinearMap
