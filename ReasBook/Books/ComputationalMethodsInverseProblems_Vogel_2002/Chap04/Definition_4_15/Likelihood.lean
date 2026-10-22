/-
Authors: Yifan Bai, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Books/ComputationalMethodsInverseProblems_Vogel_2002/README.md (Contributors).
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.Filter.Extr

public section

noncomputable section

namespace ProbabilityTheory

universe u v

/-- The fixed-data likelihood function obtained by freezing the observed data `d` in the model
`model`. -/
@[expose]
def likelihood {Θ : Type u} {Data : Type v} (model : Θ → Data → ℝ) (d : Data) : Θ → ℝ :=
  fun theta ↦ model theta d

/-- The likelihood function evaluates to the model value at the fixed data `d`. -/
theorem likelihood_apply {Θ : Type u} {Data : Type v} (model : Θ → Data → ℝ) (d : Data)
    (theta : Θ) :
    likelihood model d theta = model theta d :=
  rfl

/-- The log-likelihood function associated to the objective `L`. -/
@[expose]
def logLikelihood {Θ : Type u} (L : Θ → ℝ) : Θ → ℝ :=
  fun theta ↦ Real.log (L theta)

/-- The log-likelihood evaluates to `Real.log (L theta)` pointwise. -/
theorem logLikelihood_apply {Θ : Type u} (L : Θ → ℝ) (theta : Θ) :
    logLikelihood L theta = Real.log (L theta) :=
  rfl

/-- A parameter `thetaHat` is a maximum-likelihood estimator on `s` when it maximizes `L` on
that parameter set and belongs to it. -/
@[expose]
def IsMLEOn {Θ : Type u} (L : Θ → ℝ) (s : Set Θ) (thetaHat : Θ) : Prop :=
  thetaHat ∈ s ∧ IsMaxOn L s thetaHat

/-- `IsMLEOn L s thetaHat` means that `thetaHat` belongs to `s` and maximizes `L` on `s`. -/
theorem isMLEOn_iff {Θ : Type u} (L : Θ → ℝ) (s : Set Θ) (thetaHat : Θ) :
    IsMLEOn L s thetaHat ↔ thetaHat ∈ s ∧ IsMaxOn L s thetaHat :=
  Iff.rfl

namespace IsMLEOn

/-- An estimator on `s` lies in the parameter set `s`. -/
theorem mem {Θ : Type u} {L : Θ → ℝ} {s : Set Θ} {thetaHat : Θ}
    (h : IsMLEOn L s thetaHat) :
    thetaHat ∈ s :=
  h.1

/-- An estimator on `s` maximizes the likelihood on `s`. -/
theorem isMaxOn {Θ : Type u} {L : Θ → ℝ} {s : Set Θ} {thetaHat : Θ}
    (h : IsMLEOn L s thetaHat) :
    IsMaxOn L s thetaHat :=
  h.2

end IsMLEOn

/-- A parameter `thetaHat` is a maximum-likelihood estimator when it maximizes `L` on the full
parameter space. -/
@[expose]
def IsMLE {Θ : Type u} (L : Θ → ℝ) (thetaHat : Θ) : Prop :=
  IsMLEOn L Set.univ thetaHat

/-- `IsMLE L thetaHat` is the unrestricted `Set.univ` specialization of `IsMLEOn`. -/
theorem isMLE_iff {Θ : Type u} (L : Θ → ℝ) (thetaHat : Θ) :
    IsMLE L thetaHat ↔ IsMaxOn L Set.univ thetaHat := by
  simp [IsMLE, IsMLEOn]

/-- On a parameter set where the likelihood is strictly positive, maximizing the likelihood is
equivalent to belonging to the parameter set and maximizing the log-likelihood. -/
theorem isMLEOn_iff_isMaxOn_logLikelihood {Θ : Type u} (L : Θ → ℝ) (s : Set Θ) (thetaHat : Θ)
    (hpos : ∀ ⦃theta⦄, theta ∈ s → 0 < L theta) :
    IsMLEOn L s thetaHat ↔ thetaHat ∈ s ∧ IsMaxOn (logLikelihood L) s thetaHat := by
  constructor
  · rintro ⟨hthetaHat, hmax⟩
    have hmax' : ∀ theta ∈ s, L theta ≤ L thetaHat := by
      simpa [IsMaxOn, IsMaxFilter] using hmax
    refine ⟨hthetaHat, ?_⟩
    change ∀ theta ∈ s, Real.log (L theta) ≤ Real.log (L thetaHat)
    intro theta htheta
    exact Real.log_le_log (hpos htheta) (hmax' theta htheta)
  · rintro ⟨hthetaHat, hmax⟩
    refine ⟨hthetaHat, ?_⟩
    change ∀ theta ∈ s, L theta ≤ L thetaHat
    change ∀ theta ∈ s, Real.log (L theta) ≤ Real.log (L thetaHat) at hmax
    intro theta htheta
    exact (Real.log_le_log_iff (hpos htheta) (hpos hthetaHat)).1 (hmax theta htheta)

/-- On the full parameter space, strict positivity of the likelihood implies that maximum-
likelihood estimators are exactly the maximizers of the log-likelihood. -/
theorem isMLE_iff_isMaxOn_logLikelihood {Θ : Type u} (L : Θ → ℝ) (thetaHat : Θ)
    (hpos : ∀ theta, 0 < L theta) :
    IsMLE L thetaHat ↔ IsMaxOn (logLikelihood L) Set.univ thetaHat := by
  simpa [IsMLE, IsMLEOn] using
    (isMLEOn_iff_isMaxOn_logLikelihood L Set.univ thetaHat fun {_} _ ↦ hpos _)

end ProbabilityTheory
