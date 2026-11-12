/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Laurent

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

/-- Projection to one Laurent coefficient, summing duplicated sparse entries. -/
def laurentCoefficient (p : Laurent) (j : ℤ) : ℚ :=
  (p.map (fun e ↦ if e.1 = j then e.2 else 0)).sum

def LaurentBounded (p : Laurent) (n : ℕ) : Prop :=
  p.all (fun e ↦ decide (-(n : ℤ) ≤ e.1 ∧ e.1 ≤ n)) = true

instance (p : Laurent) (n : ℕ) : Decidable (LaurentBounded p n) :=
  inferInstanceAs (Decidable (_ = _))

theorem laurent_index_single (n : ℕ) (j : ℤ) (a : ℂ) (φ : ℤ → ℂ)
    (hj : -(n : ℤ) ≤ j ∧ j ≤ n) :
    (∑ i : Fin (2 * n + 1),
      (if j = (i.val : ℤ) - n then a else 0) * φ ((i.val : ℤ) - n)) = a * φ j := by
  have ht : (j + n).toNat < 2 * n + 1 := by omega
  let t : Fin (2 * n + 1) := ⟨(j + n).toNat, ht⟩
  have hindex : (t.val : ℤ) - n = j := by dsimp [t]; omega
  rw [Finset.sum_eq_single t]
  · rw [if_pos hindex.symm, hindex]
  · intro i _ hit
    have hne : j ≠ (i.val : ℤ) - n := by
      intro h
      apply hit
      apply Fin.ext
      have hval := congrArg (fun x : ℤ ↦ x + n) hindex
      omega
    rw [if_neg hne, zero_mul]
  · simp

/-- Sparse source expressions can be checked coefficientwise on a finite
window, with a fully proved evaluation rule for their normalization. -/
theorem laurent_projection_eval (p : Laurent) (n : ℕ) (hp : LaurentBounded p n)
    (φ : ℤ → ℂ) :
    (∑ i : Fin (2 * n + 1),
      (laurentCoefficient p ((i.val : ℤ) - n) : ℂ) * φ ((i.val : ℤ) - n)) =
      (p.map (fun e ↦ (e.2 : ℂ) * φ e.1)).sum := by
  induction p with
  | nil => simp [laurentCoefficient]
  | cons e p ih =>
    have he : -(n : ℤ) ≤ e.1 ∧ e.1 ≤ n := by
      exact of_decide_eq_true (List.all_eq_true.mp hp e List.mem_cons_self)
    have htail : LaurentBounded p n := by
      simp only [LaurentBounded, List.all_cons, Bool.and_eq_true] at hp ⊢
      exact hp.2
    simp only [laurentCoefficient, List.map_cons, List.sum_cons, Rat.cast_add,
      apply_ite, Rat.cast_zero, add_mul, Finset.sum_add_distrib]
    rw [laurent_index_single n e.1 (e.2 : ℂ) φ he]
    exact congrArg ((e.2 : ℂ) * φ e.1 + ·) (ih htail)

theorem evaluateLaurent_eq_of_coefficients (p q : Laurent) (n : ℕ)
    (hp : LaurentBounded p n) (hq : LaurentBounded q n)
    (h : ∀ i : Fin (2 * n + 1), laurentCoefficient p ((i.val : ℤ) - n) =
      laurentCoefficient q ((i.val : ℤ) - n)) (z : ℂ) :
    evaluateLaurent p z = evaluateLaurent q z := by
  rw [evaluateLaurent, evaluateLaurent,
    ← laurent_projection_eval p n hp (z ^ ·),
    ← laurent_projection_eval q n hq (z ^ ·)]
  apply Finset.sum_congr rfl
  intro i _
  rw [h i]

end ADMM.UnitCircle.LowerCertificate
