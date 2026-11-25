/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.DiscountedStability
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.Analysis.Causal.InitializedRecursion

@[expose] public section

open scoped ENNReal

namespace ADMM.UnitCircle.Causal

/-- The graph form of the two reduced proximal updates identifies their
actual discounted outputs with the selected discounted proximal operator. -/
theorem initialized_discountedProx_eq {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    {α : ℝ} (hα : 0 < α) (γ : ℝ)
    (q η w : ℕ → EuclideanSpace ℝ (Fin m))
    (hfirst : ∀ k, IsSubgradientAt (φ 0)
      (WithLp.ofLp (η k - γ • w k - q (k + 1))) (WithLp.ofLp (q (k + 1))))
    (hsecond : ∀ k, IsSubgradientAt (φ 1)
      (WithLp.ofLp (q (k + 1) + γ • w k - η (k + 1))) (WithLp.ofLp (η (k + 1)))) :
    discountedProx hφ α (initializedInputs α γ q η w) = discountedOutputs α q η := by
  have hq (k : ℕ) : proximalMapEuclidean (hφ 0) (η k - γ • w k) = q (k + 1) := by
    apply WithLp.ofLp_injective
    exact proximalMap_eq_of_subgradient (hφ 0) (by simpa using hfirst k)
  have hη (k : ℕ) : proximalMapEuclidean (hφ 1) (q (k + 1) + γ • w k) = η (k + 1) := by
    apply WithLp.ofLp_injective
    exact proximalMap_eq_of_subgradient (hφ 1) (by simpa using hsecond k)
  funext k b
  have ha : α ^ (k + 1) ≠ 0 := pow_ne_zero _ hα.ne'
  fin_cases b
  · simp [discountedProx, discountedProxBlock, initializedInputs, discountedOutputs,
      smul_smul, ← mul_assoc, inv_mul_cancel₀ ha, hq]
  · simp [discountedProx, discountedProxBlock, initializedInputs, discountedOutputs,
      smul_smul, ← mul_assoc, inv_mul_cancel₀ ha, hη]

/-- The arbitrary initialized orbit is exactly the causally constructed full
homotopy solution; uniqueness is used only on finite prefixes. -/
theorem initializedInputs_eq_discountedInput {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    {α : ℝ} (hα : 0 < α) (γ : ℝ)
    (q η w : ℕ → EuclideanSpace ℝ (Fin m))
    (hfirst : ∀ k, IsSubgradientAt (φ 0)
      (WithLp.ofLp (η k - γ • w k - q (k + 1))) (WithLp.ofLp (q (k + 1))))
    (hsecond : ∀ k, IsSubgradientAt (φ 1)
      (WithLp.ofLp (q (k + 1) + γ • w k - η (k + 1))) (WithLp.ofLp (η (k + 1))))
    (hrec : ∀ k, w (k + 1) = w k + q (k + 1) - η (k + 1)) :
    initializedInputs α γ q η w =
      discountedInput hφ α γ 1 (initialForcing α γ (η 0) (w 0)) := by
  have hy := initialized_discountedProx_eq hφ hα γ q η w hfirst hsecond
  have hv := initializedInputs_feedback α γ q η w hrec
  rw [← hy] at hv
  funext k
  apply feedback_prefix_unique (fun j b ↦ discountedProxBlock (hφ b) α j)
    α γ 1 (initialForcing α γ (η 0) (w 0)) (k + 1)
    (initializedInputs α γ q η w)
    (discountedInput hφ α γ 1 (initialForcing α γ (η 0) (w 0)))
  · intro j _
    have hvj := congrFun hv j
    unfold discountedProx at hvj
    simpa only [one_smul, Pi.add_apply] using hvj
  · intro j _
    exact homotopyInput_equation (fun j b ↦ discountedProxBlock (hφ b) α j)
      α γ 1 (initialForcing α γ (η 0) (w 0)) j
  · exact Nat.lt_succ_self k

/-- The actual state and outputs are square summable for each fixed strict
discount once the convex-supply separation estimate has provided `C`.
No bound on the initialized orbit is an assumption. -/
theorem initialized_discounted_state_memℓp {m : ℕ}
    {φ : Fin 2 → (Fin m → ℝ) → EReal} (hφ : ∀ b, IsClosedProperConvex (φ b))
    (hzero : ∀ b, IsSubgradientAt (φ b) 0 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (γ : ℝ) (q η w : ℕ → EuclideanSpace ℝ (Fin m))
    (hfirst : ∀ k, IsSubgradientAt (φ 0)
      (WithLp.ofLp (η k - γ • w k - q (k + 1))) (WithLp.ofLp (q (k + 1))))
    (hsecond : ∀ k, IsSubgradientAt (φ 1)
      (WithLp.ofLp (q (k + 1) + γ • w k - η (k + 1))) (WithLp.ofLp (η (k + 1))))
    (hrec : ∀ k, w (k + 1) = w k + q (k + 1) - η (k + 1))
    {C : ℝ} (hC : 0 < C)
    (hestimate : ∀ τ ∈ Set.Icc (0 : ℝ) 1,
      ∀ e : lp (fun _ : ℕ ↦ BlockVector m) 2,
      ∀ hv : Memℓp (discountedInput hφ α γ τ e) 2,
        ‖(⟨discountedInput hφ α γ τ e, hv⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)‖ ≤
          C * ‖e‖) :
    Memℓp (discountedOutputs α q η) 2 ∧
      Memℓp (fun k ↦ α ^ (k + 1) • w (k + 1)) 2 := by
  have he := initialForcing_memℓp hα0.le hα1 γ (η 0) (w 0)
  have hs := discountedInput_stableAt_one hφ hzero hα0 hα1 γ hC hestimate
    (⟨initialForcing α γ (η 0) (w 0), he⟩ : lp (fun _ : ℕ ↦ BlockVector m) 2)
  have hv : Memℓp (initializedInputs α γ q η w) 2 := by
    rw [initializedInputs_eq_discountedInput hφ hα0 γ q η w hfirst hsecond hrec]
    exact hs
  have hy : Memℓp (discountedOutputs α q η) 2 := by
    rw [← initialized_discountedProx_eq hφ hα0 γ q η w hfirst hsecond]
    exact discountedProx_memℓp hφ hzero hα0 _ hv
  refine ⟨hy, ?_⟩
  have hm := reconstructedMemory_memℓp hα0.le hα1 (discountedOutputs α q η) hy (w 0)
  convert! hm using 1
  funext k
  exact (reconstructedMemory_identity α q η w hrec k).symm

end ADMM.UnitCircle.Causal
