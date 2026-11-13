/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.CachedComputation
public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.ChebyshevSemantics

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open Polynomial

/-- A cache of first-kind Chebyshev coefficient lists is checked using only
integer additions, multiplication by two, and shifting by one coefficient. -/
def ChebyshevCacheValid (T : ℕ → List ℤ) (N : ℕ) : Prop :=
  T 0 = [1] ∧ T 1 = [0, 1] ∧ ∀ m : Fin (N - 1),
    T (m.val + 2) = IntegerCoefficients.add
      (0 :: IntegerCoefficients.scale 2 (T (m.val + 1)))
      (IntegerCoefficients.scale (-1) (T m))

instance (T : ℕ → List ℤ) (N : ℕ) : Decidable (ChebyshevCacheValid T N) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem chebyshevCache_sound {T : ℕ → List ℤ} {N : ℕ}
    (h : ChebyshevCacheValid T N) {m : ℕ} (hm : m ≤ N) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational (T m)) x =
      (Chebyshev.T ℝ (m : ℤ)).eval x := by
  induction m using Nat.twoStepInduction with
  | zero => simp [h.1, IntegerCoefficients.toRational]
  | one => simp [h.2.1, IntegerCoefficients.toRational]
  | more m ih0 ih1 =>
    rw [h.2.2 ⟨m, by omega⟩, IntegerCoefficients.cast_add]
    simp only [IntegerCoefficients.toRational, List.map_cons, Int.cast_zero]
    change evaluate (add (0 :: IntegerCoefficients.toRational
      (IntegerCoefficients.scale 2 (T (m + 1))))
      (IntegerCoefficients.toRational (IntegerCoefficients.scale (-1) (T m)))) x = _
    rw [evaluate_add, evaluate_cons, IntegerCoefficients.cast_scale,
      IntegerCoefficients.cast_scale, evaluate_scale, evaluate_scale,
      ih1 (by omega), ih0 (by omega)]
    have he := congrArg (fun p : ℝ[X] ↦ p.eval x) (Chebyshev.T_add_two ℝ (m : ℤ))
    simp only [eval_sub, eval_mul, eval_ofNat, eval_X] at he
    push_cast at he ⊢
    rw [he]
    norm_num
    ring

end ADMM.UnitCircle.LowerCertificate
