/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.IntegerCertificate
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
# Injective integer encodings of bounded coefficient lists

For a base larger than twice the coefficient bound, evaluation at that base
uniquely determines a fixed-length integer coefficient list. This generic
lemma is an optional certificate interface; it contains no numerical instance.
-/

namespace ADMM.UnitCircle.LowerCertificate.IntegerEncoding

/-- Ascending integer coefficients evaluated by a computable Horner fold. -/
def encoded (b : ℤ) (p : List ℤ) : ℤ :=
  p.foldr (fun a r ↦ a + b * r) 0

@[simp] theorem encoded_nil (b : ℤ) : encoded b [] = 0 := rfl

@[simp] theorem encoded_cons (b a : ℤ) (p : List ℤ) :
    encoded b (a :: p) = a + b * encoded b p := rfl

/-- Every coefficient has the specified absolute bound. -/
def Bounded (p : List ℤ) (M : ℤ) : Prop := ∀ a ∈ p, |a| ≤ M

theorem Bounded.tail {a M : ℤ} {p : List ℤ} (h : Bounded (a :: p) M) :
    Bounded p M := fun _ ha ↦ h _ (List.mem_cons_of_mem _ ha)

theorem Bounded.head {a M : ℤ} {p : List ℤ} (h : Bounded (a :: p) M) :
    |a| ≤ M := h _ (List.mem_cons_self ..)

/-- A finite Boolean bounds certificate can feed the mathematical interface. -/
theorem bounded_of_all {p : List ℤ} {M : ℤ}
    (h : p.all (fun a ↦ decide (|a| ≤ M)) = true) : Bounded p M := by
  intro a ha
  exact of_decide_eq_true ((List.all_eq_true.mp h) a ha)

theorem encoded_add (b : ℤ) (p q : List ℤ) :
    encoded b (IntegerCoefficients.add p q) = encoded b p + encoded b q := by
  induction p generalizing q with
  | nil => simp only [IntegerCoefficients.add, encoded_nil, zero_add]
  | cons a p ih =>
    cases q with
    | nil => simp only [IntegerCoefficients.add, encoded_nil, add_zero]
    | cons c q =>
      simp only [IntegerCoefficients.add, encoded_cons, ih]
      ring

theorem encoded_scale (b a : ℤ) (p : List ℤ) :
    encoded b (IntegerCoefficients.scale a p) = a * encoded b p := by
  induction p with
  | nil => simp only [IntegerCoefficients.scale, List.map_nil, encoded_nil, mul_zero]
  | cons c p ih =>
    change a * c + b * encoded b (IntegerCoefficients.scale a p) =
      a * (c + b * encoded b p)
    rw [ih]
    ring

theorem encoded_sum (b : ℤ) (ps : List (List ℤ)) :
    encoded b (IntegerCoefficients.sum ps) = (ps.map (encoded b)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change encoded b (IntegerCoefficients.add p (IntegerCoefficients.sum ps)) = _
    rw [encoded_add, ih]
    rfl

/-- A multiple strictly smaller in absolute value than its positive divisor
must vanish. This is the single-digit uniqueness step. -/
theorem eq_zero_of_dvd_of_abs_lt {b a : ℤ} (hb : 0 < b)
    (hdiv : b ∣ a) (hsmall : |a| < b) : a = 0 := by
  apply Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv
  rw [← Nat.cast_lt (α := ℤ), Int.natCast_natAbs, Int.natCast_natAbs]
  simpa only [abs_of_pos hb] using hsmall

/-- Equality of single-point encodings determines every bounded coefficient.
The length hypothesis retains any trailing zero coefficients. -/
theorem eq_of_encoded_eq {b M : ℤ} (hM : 0 ≤ M) (hb : 2 * M < b)
    {p q : List ℤ} (hlen : p.length = q.length)
    (hp : Bounded p M) (hq : Bounded q M) (heq : encoded b p = encoded b q) :
    p = q := by
  have hbpos : 0 < b := by omega
  induction p generalizing q with
  | nil =>
    cases q with
    | nil => rfl
    | cons c q => simp only [List.length_nil, List.length_cons] at hlen; omega
  | cons a p ih =>
    cases q with
    | nil => simp only [List.length_nil, List.length_cons] at hlen; omega
    | cons c q =>
      have hdvd : b ∣ a - c := by
        refine ⟨encoded b q - encoded b p, ?_⟩
        simp only [encoded_cons] at heq
        nlinarith
      have hsmall : |a - c| < b := by
        calc
          |a - c| ≤ |a| + |c| := abs_sub a c
          _ ≤ M + M := add_le_add hp.head hq.head
          _ < b := by omega
      have hac : a = c := sub_eq_zero.mp (eq_zero_of_dvd_of_abs_lt hbpos hdvd hsmall)
      subst c
      have htail : encoded b p = encoded b q := by
        simp only [encoded_cons] at heq
        exact mul_left_cancel₀ hbpos.ne' (add_left_cancel heq)
      have hlength : p.length = q.length := by
        simpa only [List.length_cons, Nat.succ.injEq] using hlen
      exact congrArg (List.cons a) (ih hlength hp.tail hq.tail htail)

@[simp] theorem encoded_replicate_zero (b : ℤ) (n : ℕ) :
    encoded b (List.replicate n 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, encoded_cons, ih, mul_zero, add_zero]

/-- In the zero case the stronger one-sided base condition `M < b` suffices. -/
theorem eq_replicate_zero_of_encoded_eq_zero {b M : ℤ}
    (hM : 0 ≤ M) (hb : M < b) {p : List ℤ}
    (hp : Bounded p M) (heq : encoded b p = 0) :
    p = List.replicate p.length 0 := by
  have hbpos : 0 < b := lt_of_le_of_lt hM hb
  induction p with
  | nil => rfl
  | cons a p ih =>
    have hdvd : b ∣ a := by
      refine ⟨-encoded b p, ?_⟩
      simp only [encoded_cons] at heq
      nlinarith
    have ha : a = 0 := eq_zero_of_dvd_of_abs_lt hbpos hdvd (hp.head.trans_lt hb)
    have ht : encoded b p = 0 := by
      simp only [encoded_cons, ha, zero_add] at heq
      exact (mul_eq_zero.mp heq).resolve_left hbpos.ne'
    simpa only [List.length_cons, List.replicate_succ, ha] using
      congrArg (List.cons a) (ih hp.tail ht)

/-- Horner evaluation in any ring, using the same ascending coefficients. -/
def horner {R : Type*} [Ring R] (x : R) (p : List ℤ) : R :=
  p.foldr (fun (a : ℤ) (r : R) ↦ (a : R) + x * r) 0

@[simp] theorem horner_nil {R : Type*} [Ring R] (x : R) : horner x [] = 0 := rfl

@[simp] theorem horner_cons {R : Type*} [Ring R] (x : R) (a : ℤ) (p : List ℤ) :
    horner x (a :: p) = (a : R) + x * horner x p := rfl

/-- The computable integer encoding is exact Horner evaluation after casting. -/
theorem cast_encoded {R : Type*} [Ring R] (b : ℤ) (p : List ℤ) :
    (encoded b p : R) = horner (b : R) p := by
  induction p with
  | nil => simp only [encoded_nil, Int.cast_zero, horner_nil]
  | cons a p ih =>
    simp only [encoded_cons, Int.cast_add, Int.cast_mul, ih, horner_cons]

/-- Agreement at a sufficiently large base gives agreement at every argument. -/
theorem horner_eq_of_encoded_eq {R : Type*} [Ring R] {b M : ℤ}
    (hM : 0 ≤ M) (hb : 2 * M < b) {p q : List ℤ}
    (hlen : p.length = q.length) (hp : Bounded p M) (hq : Bounded q M)
    (heq : encoded b p = encoded b q) (x : R) : horner x p = horner x q := by
  rw [eq_of_encoded_eq hM hb hlen hp hq heq]

/-- Compatibility with the project's rational-coefficient real evaluation. -/
theorem evaluate_toRational (p : List ℤ) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational p) x = horner x p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    change (((a : ℚ) : ℝ) + x * evaluate (IntegerCoefficients.toRational p) x) =
      (a : ℝ) + x * horner x p
    rw [Rat.cast_intCast, ih]

theorem evaluate_toRational_eq_of_encoded_eq {b M : ℤ}
    (hM : 0 ≤ M) (hb : 2 * M < b) {p q : List ℤ}
    (hlen : p.length = q.length) (hp : Bounded p M) (hq : Bounded q M)
    (heq : encoded b p = encoded b q) (x : ℝ) :
    evaluate (IntegerCoefficients.toRational p) x =
      evaluate (IntegerCoefficients.toRational q) x := by
  rw [eq_of_encoded_eq hM hb hlen hp hq heq]

end ADMM.UnitCircle.LowerCertificate.IntegerEncoding
