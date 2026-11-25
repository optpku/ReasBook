/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.FeedbackRecursion
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.DiscountedProx
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.Homotopy
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.InitialForcing

@[expose] public section

open scoped ENNReal

namespace ADMM.UnitCircle.Causal

/-- The actual discounted proximal feedback solution, constructed causally
for arbitrary forcing and every homotopy parameter. -/
noncomputable def discountedInput {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (α γ τ : ℝ) (e : ℕ → BlockVector m) : ℕ → BlockVector m :=
  homotopyInput (fun k b ↦ discountedProxBlock (hφ b) α k) α γ τ e

/-- Apply the causal homotopy to the actual discounted proximal maps.
The estimate parameter concerns solutions already in `ℓ₂`; convexity and
Parseval separation provide it in the initialized-orbit application. -/
theorem discountedInput_stableAt_one {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (γ : ℝ) {C : ℝ} (hC : 0 < C)
    (hestimate : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ∀ e : lp (fun _ : ℕ ↦ BlockVector m) 2,
      ∀ hv : Memℓp (discountedInput hφ α γ τ e) 2,
        ‖(⟨discountedInput hφ α γ τ e, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤
          C * ‖e‖) :
    StableAt (discountedInput hφ α γ) 1 := by
  let L := 1 + α + 4 * |γ| * (α / (1 - α))
  have hL : 0 ≤ L := by
    dsimp [L]
    positivity
  apply stableAt_one
    (fun v ↦ feedbackOperator α γ (discountedProx hφ α v))
    (discountedInput hφ α γ) hC hL
  · intro τ e k
    exact homotopyInput_equation (fun k b ↦ discountedProxBlock (hφ b) α k) α γ τ e k
  · intro τ e T v w hv hw
    exact feedback_prefix_unique (fun k b ↦ discountedProxBlock (hφ b) α k)
      α γ τ e T v w hv hw
  · intro v T
    exact (feedbackOperator_prefix_norm_le hα0.le hα1 γ (discountedProx hφ α v) T).trans
      (mul_le_mul_of_nonneg_left (discountedProx_prefix_norm_le hφ hzero hα0 v T) hL)
  · exact hestimate

/-- Once input membership has been established by homotopy, the actual
proximal outputs inherit membership from the proven finite-prefix estimate. -/
theorem discountedProx_memℓp {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) {α : ℝ} (hα : 0 < α)
    (v : ℕ → BlockVector m) (hv : Memℓp v 2) :
    Memℓp (discountedProx hφ α v) 2 := by
  apply memℓp_of_truncate_norm_le (B := ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖)
  intro T
  exact (discountedProx_prefix_norm_le hφ hzero hα v T).trans
    (truncate_norm_le T (⟨v, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2))

section GenericMemory

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The causal resolvent preserves `ℓ₂`, proved using the finite-prefix
bound rather than an assumed inverse operator. -/
theorem causalResolvent_memℓp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (v : ℕ → E) (hv : Memℓp v 2) : Memℓp (causalResolvent α v) 2 := by
  apply memℓp_of_truncate_norm_le
    (B := α / (1 - α) * ‖(⟨v, hv⟩ : lp (fun _ : ℕ ↦ E) 2)‖)
  intro T
  exact (causalResolvent_prefix_norm_le hα0 hα1 v T).trans
    (mul_le_mul_of_nonneg_left
      (truncate_norm_le T (⟨v, hv⟩ : lp (fun _ : ℕ ↦ E) 2))
      (div_nonneg hα0 (sub_pos.mpr hα1).le))

/-- The actual discounted state is reconstructed from the zero-state
resolvent plus the explicitly discounted initial multiplier state. -/
def reconstructedMemory (α : ℝ) (y : ℕ → Fin 2 → E) (w₀ : E) : ℕ → E :=
  (fun k ↦ y k 0 - y k 1) + causalResolvent α (fun k ↦ y k 0 - y k 1) +
    geometricTail α w₀

theorem reconstructedMemory_memℓp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    (y : ℕ → Fin 2 → E) (hy : Memℓp y 2) (w₀ : E) :
    Memℓp (reconstructedMemory α y w₀) 2 := by
  have hq : Memℓp (fun k ↦ y k 0) 2 :=
    hy.mono' (fun k ↦ norm_le_pi_norm (y k) 0)
  have hη : Memℓp (fun k ↦ y k 1) 2 :=
    hy.mono' (fun k ↦ norm_le_pi_norm (y k) 1)
  have hd : Memℓp (fun k ↦ y k 0 - y k 1) 2 := hq.sub hη
  exact (hd.add (causalResolvent_memℓp hα0 hα1 _ hd)).add
    (geometricTail_memℓp hα0 hα1 w₀)

end GenericMemory

end ADMM.UnitCircle.Causal
