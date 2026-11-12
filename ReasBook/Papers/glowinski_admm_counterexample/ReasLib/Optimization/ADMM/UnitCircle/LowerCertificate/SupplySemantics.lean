/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.LagSemantics

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open ADMM.RefinedEndpoint.Data

/-- The undamped delay and multiplier as rational Laurent expressions. -/
def delayLaurent : Laurent := [(0, 1), (-1, -1)]

def multiplierLaurent (γ : ℚ) : Laurent := [(0, 1), (-1, γ - 1)]

def pointLaurent (b i : Fin 2) : Laurent :=
  if i = 0 then [(0, 1)] else if b = 0 then delayLaurent else []

def normalLaurent (γ : ℚ) (b i : Fin 2) : Laurent :=
  if b = 0 then
    (if i = 0 then laurentScale (-1) delayLaurent
      else laurentScale (-1) (multiplierLaurent γ))
  else if i = 0 then [] else multiplierLaurent γ

theorem evaluate_delayLaurent (z : ℂ) :
    evaluateLaurent delayLaurent z = delaySymbol 1 z := by
  simp [delayLaurent, delaySymbol, zpow_neg_one, sub_eq_add_neg]

theorem evaluate_multiplierLaurent (γ : ℚ) (z : ℂ) :
    evaluateLaurent (multiplierLaurent γ) z = multiplierSymbol 1 γ z := by
  simp [multiplierLaurent, multiplierSymbol, zpow_neg_one]

theorem evaluate_pointLaurent (z : ℂ) (b i : Fin 2) :
    evaluateLaurent (pointLaurent b i) z = pointRow 1 z b i := by
  fin_cases b <;> fin_cases i <;>
    simp [pointLaurent, pointRow, evaluate_delayLaurent]

theorem evaluate_normalLaurent (γ : ℚ) (z : ℂ) (b i : Fin 2) :
    evaluateLaurent (normalLaurent γ b i) z = normalRow 1 γ z b i := by
  fin_cases b <;> fin_cases i <;>
    simp [normalLaurent, normalRow, evaluateLaurent_scale,
      evaluate_delayLaurent, evaluate_multiplierLaurent]

/-- The unsymmetrized supply is assembled from the actual normal, multiplier,
and point rows, using the same two blocks as the analytic definition. -/
def rawLaurent (γ : ℚ) (i j : Fin 2) : Laurent :=
  laurentMultiply (laurentMultiply (laurentStar (normalLaurent γ 0 i))
    (lagLaurent 0)) (pointLaurent 0 j) ++
  laurentMultiply (laurentMultiply (laurentStar (normalLaurent γ 1 i))
    (lagLaurent 1)) (pointLaurent 1 j)

theorem evaluate_rawLaurent (γ : ℚ) {z : ℂ} (hz : ‖z‖ = 1) (i j : Fin 2) :
    evaluateLaurent (rawLaurent γ i j) z = rawSupplySymbol paperWeights 1 γ z i j := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  simp [rawLaurent, evaluateLaurent_append, evaluateLaurent_multiply _ _ hz0,
    evaluateLaurent_star _ hz, evaluate_normalLaurent, evaluate_lagLaurent,
    evaluate_pointLaurent, rawSupplySymbol, Fin.sum_univ_two]

/-- Rational Laurent expression for the actual Hermitian supply matrix. -/
def supplyLaurent (γ : ℚ) (i j : Fin 2) : Laurent :=
  laurentScale (-1 / 2) (rawLaurent γ i j ++ laurentStar (rawLaurent γ j i)) ++
    if i = 1 ∧ j = 1 then
      laurentScale (-epsilon) (laurentMultiply delayLaurent (laurentStar delayLaurent))
    else []

/-- Every generated rational supply entry evaluates to the original analytic
matrix entry. In particular subsequent rational identities retain their source. -/
theorem evaluate_supplyLaurent (γ : ℚ) {z : ℂ} (hz : ‖z‖ = 1) (i j : Fin 2) :
    evaluateLaurent (supplyLaurent γ i j) z = supplySymbol paperWeights 1 γ z i j := by
  have hz0 : z ≠ 0 := by intro h; simp [h] at hz
  have hnorm : delaySymbol 1 z * star (delaySymbol 1 z) =
      (Complex.normSq (delaySymbol 1 z) : ℂ) := by
    simpa only [Complex.star_def] using Complex.mul_conj (delaySymbol 1 z)
  fin_cases i <;> fin_cases j <;>
    simp [supplyLaurent, evaluateLaurent_append, evaluateLaurent_scale,
      evaluate_rawLaurent _ hz, evaluateLaurent_star _ hz,
      evaluateLaurent_multiply _ _ hz0, evaluate_delayLaurent, hnorm,
      supplySymbol, hermitianPart, Matrix.conjTranspose_apply,
      residualCoordinateMatrix, paperWeights] <;> try ring
  simp only [Complex.star_def] at hnorm
  rw [← hnorm]
  ring

end ADMM.UnitCircle.LowerCertificate
