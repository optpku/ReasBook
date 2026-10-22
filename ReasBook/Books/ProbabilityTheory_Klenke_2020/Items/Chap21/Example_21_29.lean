/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Example_21_29Core

open scoped BigOperators

universe u

namespace ProbabilityTheory

variable {Ω : Type u}

/-- Helper for Example 21.29: the finite-increment value assigned to a step integrand along a path
`W`. -/
def paleyWienerStepIntegral
    (W : NNReal → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → NNReal) (α : Fin n → ℝ) :
    Ω → ℝ :=
  fun ω ↦ ∑ i : Fin n, α i * (W (t i.succ) ω - W (t i.castSucc) ω)

/-- Helper for Example 21.29: evaluating `paleyWienerStepIntegral` expands to the defining
increment sum. -/
@[simp] theorem paleyWienerStepIntegral_apply
    (W : NNReal → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → NNReal) (α : Fin n → ℝ) (ω : Ω) :
    paleyWienerStepIntegral W t α ω =
      ∑ i : Fin n, α i * (W (t i.succ) ω - W (t i.castSucc) ω) :=
  rfl

/-- Helper for Example 21.29: for a step integrand `f = ∑ᵢ αᵢ 𝟙_(tᵢ, tᵢ₊₁]`, the
Paley--Wiener stochastic integral along `W` is the finite increment sum
`∑ᵢ αᵢ (W_{tᵢ₊₁} - W_{tᵢ})`. -/
theorem paleyWienerStepIntegral_eq_incrementSum
    (W : NNReal → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → NNReal) (α : Fin n → ℝ) (ω : Ω) :
    paleyWienerStepIntegral W t α ω =
      ∑ i : Fin n, α i * (W (t i.succ) ω - W (t i.castSucc) ω) := by
  -- Proof comment: the owner theorem is exactly the defining expansion of the step integral.
  rfl

/-- Example 21.29: for a step integrand `f = ∑ᵢ αᵢ 𝟙_(tᵢ, tᵢ₊₁]`, the Paley--Wiener stochastic
integral along `W` is the finite increment sum `∑ᵢ αᵢ (W_{tᵢ₊₁} - W_{tᵢ})`. -/
theorem paleyWienerIntegralL2_hasGaussianLaw
    (W : NNReal → Ω → ℝ) {n : ℕ} (t : Fin (n + 1) → NNReal) (α : Fin n → ℝ) (ω : Ω) :
    paleyWienerStepIntegral W t α ω =
      ∑ i : Fin n, α i * (W (t i.succ) ω - W (t i.castSucc) ω) := by
  -- Proof comment: the label-bearing item theorem is the same step-integral identity.
  exact paleyWienerStepIntegral_eq_incrementSum W t α ω

end ProbabilityTheory
