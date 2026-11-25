/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.MomentRegrouping
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Coefficients

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

/-- A sparse rational Laurent expression. Duplicated exponents are summed,
so algebraic operations can be evaluated and checked without quotient reduction. -/
abbrev Laurent := List (ℤ × ℚ)

noncomputable def evaluateLaurent (p : Laurent) (z : ℂ) : ℂ :=
  (p.map (fun e ↦ (e.2 : ℂ) * z ^ e.1)).sum

def laurentScale (a : ℚ) (p : Laurent) : Laurent := p.map (fun e ↦ (e.1, a * e.2))

def laurentMultiply (p q : Laurent) : Laurent :=
  p.flatMap (fun e ↦ q.map (fun f ↦ (e.1 + f.1, e.2 * f.2)))

def laurentStar (p : Laurent) : Laurent := p.map (fun e ↦ (-e.1, e.2))

@[simp] theorem evaluateLaurent_nil (z : ℂ) : evaluateLaurent [] z = 0 := rfl

@[simp] theorem evaluateLaurent_cons (e : ℤ × ℚ) (p : Laurent) (z : ℂ) :
    evaluateLaurent (e :: p) z = (e.2 : ℂ) * z ^ e.1 + evaluateLaurent p z := rfl

theorem evaluateLaurent_append (p q : Laurent) (z : ℂ) :
    evaluateLaurent (p ++ q) z = evaluateLaurent p z + evaluateLaurent q z := by
  simp [evaluateLaurent]

theorem evaluateLaurent_scale (a : ℚ) (p : Laurent) (z : ℂ) :
    evaluateLaurent (laurentScale a p) z = (a : ℂ) * evaluateLaurent p z := by
  induction p with
  | nil => simp [laurentScale]
  | cons e p ih =>
    change ((a * e.2 : ℚ) : ℂ) * z ^ e.1 + evaluateLaurent (laurentScale a p) z = _
    rw [Rat.cast_mul, ih, evaluateLaurent_cons]
    ring

theorem evaluateLaurent_multiply (p q : Laurent) {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (laurentMultiply p q) z =
      evaluateLaurent p z * evaluateLaurent q z := by
  induction p with
  | nil => simp [laurentMultiply]
  | cons e p ih =>
    change evaluateLaurent ((q.map (fun f ↦ (e.1 + f.1, e.2 * f.2))) ++
      laurentMultiply p q) z = _
    rw [evaluateLaurent_append, ih, evaluateLaurent_cons]
    have h : evaluateLaurent (q.map (fun f ↦ (e.1 + f.1, e.2 * f.2))) z =
        (e.2 : ℂ) * z ^ e.1 * evaluateLaurent q z := by
      simp only [evaluateLaurent, List.map_map]
      rw [← List.sum_map_mul_left]
      apply congrArg List.sum
      apply List.map_congr_left
      intro f _
      simp only [Function.comp_apply, Rat.cast_mul, zpow_add₀ hz]
      ring
    rw [h]
    ring

theorem evaluateLaurent_star (p : Laurent) {z : ℂ} (hz : ‖z‖ = 1) :
    evaluateLaurent (laurentStar p) z = star (evaluateLaurent p z) := by
  induction p with
  | nil => simp [laurentStar]
  | cons e p ih =>
    change (e.2 : ℂ) * z ^ (-e.1) + evaluateLaurent (laurentStar p) z = _
    rw [ih, evaluateLaurent_cons, star_add, star_mul]
    simp only [star_zpow₀, Complex.star_def, ← Complex.inv_eq_conj hz,
      inv_zpow, zpow_neg, map_ratCast]
    ring

end ADMM.UnitCircle.LowerCertificate
