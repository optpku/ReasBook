module

public import ReasLib.Analysis.Calculus.FiniteTaylorJet.CubicUniformBound

public section

/-!
# Uniform cubic bounds from vanishing derivatives

This file converts joint finite differentiability and vanishing slice derivatives into the
uniform finite-jet hypotheses used by `CubicUniformBound`.
-/

open Filter
open scoped Topology

universe u v

namespace FiniteTaylorJet

variable {Theta : Type u} {F : Type v}
variable [NormedAddCommGroup Theta] [NormedSpace ℝ Theta]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable contraction):
a jointly `C³` scalar-input family on a compact parameter set is uniformly cubic when its
slice derivatives of orders zero, one, and two vanish.  This also supplies the finite-jet
form of the transverse cubic estimate required by Lemma 4.15. -/
theorem exists_cubic_bound_of_contDiffAt_of_iteratedFDeriv_eq_zero
    {f : Theta → ℝ → F} {K : Set Theta}
    (hK : IsCompact K)
    (hf : ∀ theta ∈ K,
      ContDiffAt ℝ 3 (Function.uncurry f) (theta, 0))
    (hzero : ∀ theta ∈ K, ∀ n : ℕ, n < 3 →
      iteratedFDeriv ℝ n (f theta) 0 = 0) :
    ∃ C > 0, ∃ delta > 0, ∀ theta ∈ K, ∀ h : ℝ, ‖h‖ < delta →
      ‖f theta h‖ ≤ C * ‖h ^ (3 : ℕ)‖ := by
  have huniform := isUniformOn_of_contDiffAt 3 f 0 K hK hf
  have hcoeffZero : ∀ theta ∈ K, ∀ n : Fin 4, (n : ℕ) < 3 →
      (ofFunction ℝ 3 (f theta) 0).coeff n = 0 := by
    intro theta htheta n hn
    rw [coeff_ofFunction, hzero theta htheta n hn, smul_zero]
  exact huniform.exists_cubic_bound_of_coeff_zero hcoeffZero

/-- Helper for Infrastructure I.16 (Finite-smooth invariant graph under an explicit stable
contraction): if the compact parameter set is also a neighborhood of `theta0`, the uniform
cubic derivative estimate holds eventually near `(0, theta0)`. -/
theorem eventually_cubic_bound_of_contDiffAt_of_iteratedFDeriv_eq_zero
    {f : Theta → ℝ → F} {K : Set Theta} {theta0 : Theta}
    (hKcompact : IsCompact K) (hKneighborhood : K ∈ 𝓝 theta0)
    (hf : ∀ theta ∈ K,
      ContDiffAt ℝ 3 (Function.uncurry f) (theta, 0))
    (hzero : ∀ theta ∈ K, ∀ n : ℕ, n < 3 →
      iteratedFDeriv ℝ n (f theta) 0 = 0) :
    ∃ C > 0, ∀ᶠ x : ℝ × Theta in 𝓝 (0, theta0),
      ‖f x.2 x.1‖ ≤ C * ‖x.1 ^ (3 : ℕ)‖ := by
  have huniform := isUniformOn_of_contDiffAt 3 f 0 K hKcompact hf
  have hcoeffZero : ∀ theta ∈ K, ∀ n : Fin 4, (n : ℕ) < 3 →
      (ofFunction ℝ 3 (f theta) 0).coeff n = 0 := by
    intro theta htheta n hn
    rw [coeff_ofFunction, hzero theta htheta n hn, smul_zero]
  exact huniform.eventually_cubic_bound_of_coeff_zero hKneighborhood hcoeffZero

end FiniteTaylorJet
