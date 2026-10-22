/-
Authors: Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Upstream attribution: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/README.md (formalization author).
Upstream source: https://github.com/imathwy/DFP_wolfe_local/blob/e308927f5b7930bdd002f0c0e42b9d112ad821cb/DFPWolfe/Required_Lean_mathlib_Infrastructure_for_the_DFP_Counterexample/Infrastructure_I_22_Vanishing_step_unbounded_winding_approaches_every_angle_modu.lean
-/

module

public import ReasLib.Topology.Circle.VanishingStep

public section

open Filter
open scoped Topology

/-Infrastructure I.22 (Vanishing-step unbounded winding approaches every angle modulo $2\pi$) (1) -/
#check (Real.existsSubseqAddIntMulTendsto (2 * Real.pi) Real.two_pi_pos :
  ∀ {φ : ℕ → ℝ}, StrictAnti φ → Tendsto φ atTop atBot →
    Tendsto (fun j : ℕ ↦ φ j - φ (j + 1)) atTop (𝓝 0) → ∀ θ : ℝ,
      ∃ j : ℕ → ℕ, ∃ m : ℕ → ℤ, StrictMono j ∧
        Tendsto (fun i ↦ φ (j i) + m i * (2 * Real.pi)) atTop (𝓝 θ))

/-Infrastructure I.22 (Vanishing-step unbounded winding approaches every angle modulo $2\pi$) (2) -/
#check (Circle.mapClusterPtExpOfVanishingStep :
  ∀ {φ : ℕ → ℝ}, StrictAnti φ → Tendsto φ atTop atBot →
    Tendsto (fun j : ℕ ↦ φ j - φ (j + 1)) atTop (𝓝 0) → ∀ z : Circle,
      MapClusterPt z atTop (fun j ↦ Circle.exp (φ j)))
