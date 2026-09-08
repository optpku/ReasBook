module

public import ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion
import all ReasLib.Optimization.DFP.TwoPhaseControls.MixedExpansion

public section

noncomputable section

open scoped Topology

namespace DFP.TwoLeg.Mixed

/-!
This file contains coefficient-extraction adapters for the independent-radius mixed
expansion.  They keep the analytic and algebraic parts of a proof separate: a caller only
has to provide the regularity and the first few iterated derivatives of a scalar path.
-/

/-- Regularity and the first two iterated derivatives produce
the factorial-normalized three-coefficient radius germ `[0, 1, c]`. -/
theorem independentRadiusTruncatedGerm_of_threeDerivativeData
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {c : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 3 (Function.uncurry f) (θ, 0))
    (hzero : ∀ θ, θ ∈ K → f θ 0 = 0)
    (hlinear : ∀ θ, θ ∈ K → iteratedDeriv 1 (f θ) 0 = 1)
    (hquadratic : ∀ θ, θ ∈ K → iteratedDeriv 2 (f θ) 0 = 2 * c θ) :
    IndependentRadiusTruncatedGerm f K 3
      (fun n θ ↦ (![0, 1, c θ] : Fin 3 → ℝ) n) := by
  refine ⟨hregular, ?_⟩
  intro n θ hθ
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  fin_cases n
  · simp [hzero θ hθ]
  · simp [hlinear θ hθ]
  · norm_num [hquadratic θ hθ]
    ring

/-- Regularity and the value/linear derivative data produce
the factorial-normalized two-coefficient germ `[c₀, c₁]`. -/
theorem independentRadiusTruncatedGerm_of_twoDerivativeData
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)}
    {c₀ c₁ : (ℝ × ℝ × ℝ) → ℝ}
    (hregular : ∀ θ, θ ∈ K →
      ContDiffAt ℝ 2 (Function.uncurry f) (θ, 0))
    (hzero : ∀ θ, θ ∈ K → f θ 0 = c₀ θ)
    (hlinear : ∀ θ, θ ∈ K → iteratedDeriv 1 (f θ) 0 = c₁ θ) :
    IndependentRadiusTruncatedGerm f K 2
      (fun n θ ↦ (![c₀ θ, c₁ θ] : Fin 2 → ℝ) n) := by
  refine ⟨hregular, ?_⟩
  intro n θ hθ
  rw [FiniteTaylorJet.scalarCoeff_ofFunction]
  fin_cases n
  · simp [hzero θ hθ]
  · simp [hlinear θ hθ]

/- The following adapters align the full coefficient indexing with the
   truncated interface used by the compact remainder estimates. -/

/-- Infrastructure I.16a: a full independent-radius coefficient germ restricts to the
lower coefficients retained by the truncated germ interface. -/
theorem independentRadiusTruncatedGerm_of_coefficientGerm
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ}
    (hGerm : IndependentRadiusCoefficientGerm f K m coeff) :
    IndependentRadiusTruncatedGerm f K m
      (fun n θ ↦ coeff n.castSucc θ) := by
  refine ⟨hGerm.regularity, ?_⟩
  intro n θ hθ
  exact hGerm.coefficient_eq n.castSucc θ hθ

/-- Helper for Infrastructure I.16a: a truncated independent-radius coefficient germ and
an explicit top-coefficient identity reconstruct the full coefficient germ. -/
theorem independentRadiusCoefficientGerm_of_truncatedGerm
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ}
    (hGerm : IndependentRadiusTruncatedGerm f K m
      (fun n θ ↦ coeff n.castSucc θ))
    (htop : ∀ θ, θ ∈ K →
      (FiniteTaylorJet.ofFunction ℝ m (f θ) 0).scalarCoeff (Fin.last m) =
        coeff (Fin.last m) θ) :
    IndependentRadiusCoefficientGerm f K m coeff := by
  refine ⟨hGerm.regularity, ?_⟩
  intro n θ hθ
  refine Fin.lastCases ?_ (fun i => ?_) n
  · exact htop θ hθ
  · exact hGerm.coefficient_eq i θ hθ

/-- Helper for Infrastructure I.16a: a truncated coefficient germ together with its top
coefficient identity supplies the compact-uniform remainder estimate directly. -/
theorem uniformRemainderOn_of_truncatedGerm_and_topCoefficient
    {f : (ℝ × ℝ × ℝ) → ℝ → ℝ} {K : Set (ℝ × ℝ × ℝ)} {m : ℕ}
    {coeff : Fin (m + 1) → (ℝ × ℝ × ℝ) → ℝ}
    (hK : IsCompact K)
    (hGerm : IndependentRadiusTruncatedGerm f K m
      (fun n θ ↦ coeff n.castSucc θ))
    (htop : ∀ θ, θ ∈ K →
      (FiniteTaylorJet.ofFunction ℝ m (f θ) 0).scalarCoeff (Fin.last m) =
        coeff (Fin.last m) θ)
    (C : ℝ) (hC : 0 < C) :
    Asymptotics.IsUniformRemainderOn
      (fun θ r ↦ f θ r - ∑ n : Fin (m + 1), coeff n θ * r ^ (n : ℕ))
      K C (m : ℝ) := by
  exact uniformRemainderOn_of_independentRadiusGerm hK
    (independentRadiusCoefficientGerm_of_truncatedGerm hGerm htop) C hC

end DFP.TwoLeg.Mixed
