/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.LowerCertificate.Division.ActualDivision

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate.Determinant

namespace Integer

def add : List ℤ → List ℤ → List ℤ
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

def scale (a : ℤ) (p : List ℤ) : List ℤ := p.map (a * ·)

def multiply : List ℤ → List ℤ → List ℤ
  | [], _ => []
  | _, [] => []
  | a :: p, q => add (scale a q) (0 :: multiply p q)

def subtract (p q : List ℤ) : List ℤ := add p (scale (-1) q)

def monomial (n : ℕ) (a : ℤ) : List ℤ := List.replicate n 0 ++ [a]

/-- Ascending integer coefficients, evaluated by Horner recursion over ℂ. -/
noncomputable def evaluate : List ℤ → ℂ → ℂ
  | [], _ => 0
  | a :: p, z => (a : ℂ) + z * evaluate p z

@[simp] theorem evaluate_nil (z : ℂ) : evaluate [] z = 0 := rfl
@[simp] theorem evaluate_cons (a : ℤ) (p : List ℤ) (z : ℂ) :
    evaluate (a :: p) z = (a : ℂ) + z * evaluate p z := rfl

theorem evaluate_add (p q : List ℤ) (z : ℂ) :
    evaluate (add p q) z = evaluate p z + evaluate q z := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

theorem evaluate_scale (a : ℤ) (p : List ℤ) (z : ℂ) :
    evaluate (scale a p) z = (a : ℂ) * evaluate p z := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change ((a * b : ℤ) : ℂ) + z * evaluate (scale a p) z = _
    rw [Int.cast_mul, ih, evaluate_cons]
    ring

/-- Integer convolution is sound without rational normalization inside the
large certificate computation. -/
theorem evaluate_multiply (p q : List ℤ) (z : ℂ) :
    evaluate (multiply p q) z = evaluate p z * evaluate q z := by
  induction p generalizing q with
  | nil => simp [multiply]
  | cons a p ih =>
    cases q with
    | nil => simp [multiply]
    | cons b q => simp [multiply, evaluate_add, evaluate_scale, ih]; ring

theorem evaluate_subtract (p q : List ℤ) (z : ℂ) :
    evaluate (subtract p q) z = evaluate p z - evaluate q z := by
  rw [subtract, evaluate_add, evaluate_scale]
  push_cast
  ring

theorem evaluate_monomial (n : ℕ) (a : ℤ) (z : ℂ) :
    evaluate (monomial n a) z = (a : ℂ) * z ^ n := by
  induction n with
  | zero => simp [monomial]
  | succ n ih =>
    simp only [monomial, List.replicate_succ, List.cons_append, evaluate_cons,
      Int.cast_zero, zero_add] at ih ⊢
    rw [ih, pow_succ]
    ring

end Integer

/-- A dense integer vector with an exact common denominator and Laurent offset. -/
def rationalLaurent (offset : ℤ) (denominator : ℤ) : List ℤ → Laurent
  | [] => []
  | a :: p => (offset, (a : ℚ) / (denominator : ℚ)) :: rationalLaurent (offset + 1) denominator p

/-- The dense integer representation has a fully proved exact evaluation. -/
theorem evaluate_rationalLaurent (offset denominator : ℤ) (p : List ℤ)
    {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent offset denominator p) z =
      z ^ offset / (denominator : ℂ) * Integer.evaluate p z := by
  induction p generalizing offset with
  | nil => simp [rationalLaurent]
  | cons a p ih =>
    rw [rationalLaurent, evaluateLaurent_cons, ih, Integer.evaluate_cons]
    simp only [Rat.cast_div, Rat.cast_intCast, zpow_add₀ hz, zpow_one]
    ring

/-- Zero-padded addition commutes with the Laurent representation. -/
theorem evaluate_rationalLaurent_add (offset denominator : ℤ) (p q : List ℤ)
    {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent offset denominator (Integer.add p q)) z =
      evaluateLaurent (rationalLaurent offset denominator p) z +
        evaluateLaurent (rationalLaurent offset denominator q) z := by
  simp only [evaluate_rationalLaurent _ _ _ hz, Integer.evaluate_add]
  ring

theorem evaluate_rationalLaurent_scale (offset denominator a : ℤ) (p : List ℤ)
    {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent offset denominator (Integer.scale a p)) z =
      (a : ℂ) * evaluateLaurent (rationalLaurent offset denominator p) z := by
  simp only [evaluate_rationalLaurent _ _ _ hz, Integer.evaluate_scale]
  ring

/-- A numerator monomial at index `n` gives a constant after offset `-n`. -/
theorem evaluate_rationalLaurent_monomial (n : ℕ) (denominator a : ℤ)
    {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent (-(n : ℤ)) denominator (Integer.monomial n a)) z =
      (a : ℂ) / (denominator : ℂ) := by
  rw [evaluate_rationalLaurent _ _ _ hz, Integer.evaluate_monomial]
  have hp : z ^ (-(n : ℤ)) * z ^ n = 1 := by
    rw [← zpow_natCast, ← zpow_add₀ hz]
    simp
  calc
    _ = ((a : ℂ) / (denominator : ℂ)) * (z ^ (-(n : ℤ)) * z ^ n) := by ring
    _ = _ := by rw [hp, mul_one]

/-- Convolution adds Laurent offsets and multiplies the common denominators. -/
theorem evaluate_rationalLaurent_multiply (a b D E : ℤ) (p q : List ℤ)
    {z : ℂ} (hz : z ≠ 0) :
    evaluateLaurent (rationalLaurent (a + b) (D * E) (Integer.multiply p q)) z =
      evaluateLaurent (rationalLaurent a D p) z *
        evaluateLaurent (rationalLaurent b E q) z := by
  simp only [evaluate_rationalLaurent _ _ _ hz, Integer.evaluate_multiply,
    zpow_add₀ hz, Int.cast_mul]
  ring

/-- Reversing the finite source list does not change its Laurent evaluation. -/
theorem evaluateLaurent_reverse (p : Laurent) (z : ℂ) :
    evaluateLaurent p.reverse z = evaluateLaurent p z := by
  simp only [evaluateLaurent, List.map_reverse, List.sum_reverse]

end ADMM.UnitCircle.LowerCertificate.Determinant
