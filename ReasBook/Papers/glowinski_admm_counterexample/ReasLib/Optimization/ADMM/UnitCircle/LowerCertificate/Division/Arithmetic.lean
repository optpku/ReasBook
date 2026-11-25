/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.LaurentExtensionality
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.SupplySemantics

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Division

@[simp] theorem coefficient_nil (j : ℤ) : laurentCoefficient [] j = 0 := rfl

@[simp] theorem coefficient_cons (e : ℤ × ℚ) (p : Laurent) (j : ℤ) :
    laurentCoefficient (e :: p) j = (if e.1 = j then e.2 else 0) +
      laurentCoefficient p j := rfl

@[simp] theorem coefficient_append (p q : Laurent) (j : ℤ) :
    laurentCoefficient (p ++ q) j = laurentCoefficient p j + laurentCoefficient q j := by
  simp [laurentCoefficient]

@[simp] theorem coefficient_scale (a : ℚ) (p : Laurent) (j : ℤ) :
    laurentCoefficient (laurentScale a p) j = a * laurentCoefficient p j := by
  induction p with
  | nil => simp [laurentScale]
  | cons e p ih =>
    change (if e.1 = j then a * e.2 else 0) +
      laurentCoefficient (laurentScale a p) j =
      a * ((if e.1 = j then e.2 else 0) + laurentCoefficient p j)
    rw [ih]
    by_cases h : e.1 = j <;> simp [h, mul_add]

@[simp] theorem coefficient_star (p : Laurent) (j : ℤ) :
    laurentCoefficient (laurentStar p) j = laurentCoefficient p (-j) := by
  induction p with
  | nil => rfl
  | cons e p ih =>
    change (if -e.1 = j then e.2 else 0) + laurentCoefficient (laurentStar p) j =
      (if e.1 = -j then e.2 else 0) + laurentCoefficient p (-j)
    rw [ih]
    have h : -e.1 = j ↔ e.1 = -j := by omega
    simp only [h]

/-- Coefficients of a monomial times a Laurent expression require one lookup,
rather than expansion of a long sparse product. -/
theorem coefficient_monomial (a : ℤ) (c : ℚ) (p : Laurent) (j : ℤ) :
    laurentCoefficient (p.map (fun e ↦ (a + e.1, c * e.2))) j =
      c * laurentCoefficient p (j - a) := by
  induction p with
  | nil => simp
  | cons e p ih =>
    simp only [List.map_cons, coefficient_cons, ih]
    have h : a + e.1 = j ↔ e.1 = j - a := by omega
    simp only [h]
    by_cases he : e.1 = j - a <;> simp [he, mul_add]

/-- A short left Laurent factor gives a short linear combination of shifted
coefficient lookups. -/
@[simp] theorem coefficient_multiply_cons (e : ℤ × ℚ) (p q : Laurent) (j : ℤ) :
    laurentCoefficient (laurentMultiply (e :: p) q) j =
      e.2 * laurentCoefficient q (j - e.1) +
        laurentCoefficient (laurentMultiply p q) j := by
  change laurentCoefficient ((q.map (fun f ↦ (e.1 + f.1, e.2 * f.2))) ++
    laurentMultiply p q) j = _
  rw [coefficient_append, coefficient_monomial]

@[simp] theorem coefficient_multiply_nil (p : Laurent) (j : ℤ) :
    laurentCoefficient (laurentMultiply [] p) j = 0 := rfl

end ADMM.UnitCircle.LowerCertificate.Division
