/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Determinant.DirectCoefficients

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

/-- Complete finite coefficient checks recover the original integer vector
identity, using the independently proved degree and coefficient formulas. -/
theorem determinantVector_eq_of_coefficients {r a b c : List ℤ}
    (hr : r.length = 1025) (ha : a.length = 513) (hb : b.length = 513) (hc : c.length = 513)
    {A B C : ℕ → ℤ} (hA : ∀ k, A k = a.getD k 0)
    (hB : ∀ k, B k = b.getD k 0) (hC : ∀ k, C k = c.getD k 0)
    (h : ∀ i : Fin 1025, r.getD i.val 0 = directDeterminantCoefficient A B C i.val) :
    r = determinantVector a b c := by
  have hl := determinantVector_length ha hb hc
  apply List.ext_getElem (hr.trans hl.symm)
  intro i hir hiv
  have hi : i < 1025 := by omega
  have hval := h ⟨i, hi⟩
  rw [directDeterminantCoefficient_eq ha hb hc hA hB hC i] at hval
  simpa only [List.getD_eq_getElem r 0 hir,
    List.getD_eq_getElem (determinantVector a b c) 0 hiv] using hval

theorem startDeterminant_length : startDeterminantNumerators.length = 1025 := by decide +kernel

theorem lowerDeterminant_length : lowerDeterminantNumerators.length = 1025 := by decide +kernel

end ADMM.UnitCircle.LowerCertificate.Determinant
