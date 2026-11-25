/-
Authors: Qiming Dai
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f40e785158f79d8f0e645890825b840af912e327:ReasBook/Papers/glowinski_admm_counterexample/README.md (formalization contributor).
-/

module

public import glowinski_admm_counterexample.ReasLib.Optimization.ADMM.UnitCircle.BernsteinCertificate

@[expose] public section

namespace ADMM.UnitCircle.LowerCertificate

open scoped BigOperators

/-- Ascending rational power coefficients. This representation has computable
arithmetic, unlike deciding equality of quotient-based `Polynomial` values. -/
abbrev Coefficients := List ℚ

/-- Real evaluation by Horner's rule. -/
noncomputable def evaluate : Coefficients → ℝ → ℝ
  | [], _ => 0
  | a :: p, x => (a : ℝ) + x * evaluate p x

/-- Addition with zero padding. -/
def add : Coefficients → Coefficients → Coefficients
  | [], q => q
  | p, [] => p
  | a :: p, b :: q => (a + b) :: add p q

/-- Rational scalar multiplication. -/
def scale (a : ℚ) (p : Coefficients) : Coefficients := p.map (a * ·)

/-- Convolution, arranged as Horner recursion in the first input. -/
def multiply : Coefficients → Coefficients → Coefficients
  | [], _ => []
  | _, [] => []
  | a :: p, q => add (scale a q) (0 :: multiply p q)

/-- Natural powers in the coefficient representation. -/
def power (p : Coefficients) : ℕ → Coefficients
  | 0 => [1]
  | n + 1 => multiply p (power p n)

/-- Composition, again by Horner recursion. -/
def compose : Coefficients → Coefficients → Coefficients
  | [], _ => []
  | a :: p, q => add [a] (multiply q (compose p q))

@[simp] theorem evaluate_nil (x : ℝ) : evaluate [] x = 0 := rfl

@[simp] theorem evaluate_cons (a : ℚ) (p : Coefficients) (x : ℝ) :
    evaluate (a :: p) x = a + x * evaluate p x := rfl

theorem evaluate_add (p q : Coefficients) (x : ℝ) :
    evaluate (add p q) x = evaluate p x + evaluate q x := by
  induction p generalizing q with
  | nil => simp [add]
  | cons a p ih =>
    cases q with
    | nil => simp [add]
    | cons b q => simp [add, ih]; ring

theorem evaluate_scale (a : ℚ) (p : Coefficients) (x : ℝ) :
    evaluate (scale a p) x = a * evaluate p x := by
  induction p with
  | nil => simp [scale]
  | cons b p ih =>
    change ((a * b : ℚ) : ℝ) + x * evaluate (scale a p) x =
      (a : ℝ) * ((b : ℝ) + x * evaluate p x)
    rw [Rat.cast_mul, ih]
    ring

theorem evaluate_multiply (p q : Coefficients) (x : ℝ) :
    evaluate (multiply p q) x = evaluate p x * evaluate q x := by
  induction p generalizing q with
  | nil => simp [multiply]
  | cons a p ih =>
    cases q with
    | nil => simp [multiply]
    | cons b q => simp [multiply, evaluate_add, evaluate_scale, ih]; ring

theorem evaluate_power (p : Coefficients) (n : ℕ) (x : ℝ) :
    evaluate (power p n) x = evaluate p x ^ n := by
  induction n with
  | zero => simp [power]
  | succ n ih => simp [power, evaluate_multiply, ih, pow_succ, mul_comm]

theorem evaluate_compose (p q : Coefficients) (x : ℝ) :
    evaluate (compose p q) x = evaluate p (evaluate q x) := by
  induction p with
  | nil => simp [compose]
  | cons a p ih => simp [compose, evaluate_add, evaluate_multiply, ih]

/-- Exact power coefficients of one Bernstein basis polynomial. -/
def basis (n k : ℕ) : Coefficients :=
  scale (Nat.fast_choose n k : ℚ) (multiply (power [0, 1] k) (power [1, -1] (n - k)))

theorem evaluate_basis (n k : ℕ) (x : unitInterval) :
    evaluate (basis n k) x = bernstein n k x := by
  simp [basis, ← Nat.choose_eq_fast_choose, evaluate_scale, evaluate_multiply,
    evaluate_power, bernstein_apply,
    sub_eq_add_neg, mul_assoc]

/-- Sum a list of coefficient vectors. -/
def sum : List Coefficients → Coefficients := List.foldr add []

theorem evaluate_sum (ps : List Coefficients) (x : ℝ) :
    evaluate (sum ps) x = (ps.map (fun p ↦ evaluate p x)).sum := by
  induction ps with
  | nil => simp [sum]
  | cons p ps ih =>
    change evaluate (add p (sum ps)) x =
      evaluate p x + (ps.map (fun p ↦ evaluate p x)).sum
    rw [evaluate_add, ih]

/-- Bernstein expansion over rationals, kept in a computational representation. -/
def expansion (n : ℕ) (c : Fin (n + 1) → ℚ) : Coefficients :=
  sum (List.ofFn (fun k : Fin (n + 1) ↦ scale (c k) (basis n k)))

theorem evaluate_expansion (n : ℕ) (c : Fin (n + 1) → ℚ) (x : unitInterval) :
    evaluate (expansion n c) x =
      ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k x := by
  unfold expansion
  rw [evaluate_sum, List.map_ofFn, List.sum_ofFn]
  apply Finset.sum_congr rfl
  intro k _
  change evaluate (scale (c k) (basis n k)) (x : ℝ) = _
  rw [evaluate_scale, evaluate_basis]

/-- Kernel-verified coefficient equality and positive Bernstein coefficients
prove positivity on the entire certified subinterval. -/
theorem positive_on_interval (p : Coefficients) (a b : ℚ) (hab : a < b)
    (n : ℕ) (c : Fin (n + 1) → ℚ) (δ : ℚ) (hδ : 0 < δ)
    (hc : ∀ k, δ ≤ c k)
    (heq : compose p [a, b - a] = expansion n c)
    {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) (b : ℝ)) : 0 < evaluate p x := by
  have hba : 0 < (b : ℝ) - a := by exact_mod_cast sub_pos.mpr hab
  let t : unitInterval := ⟨(x - a) / (b - a), by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hx.1) hba.le
    · exact (div_le_one hba).mpr (sub_le_sub_right hx.2 a)⟩
  have ht : evaluate [a, b - a] (t : ℝ) = x := by
    simp only [evaluate_cons, evaluate_nil, mul_zero, add_zero, Rat.cast_sub]
    dsimp [t]
    rw [mul_comm ((x - a) / (b - a)), mul_div_cancel₀ _ (ne_of_gt hba)]
    ring
  have hs : (δ : ℝ) ≤ evaluate (expansion n c) t := by
    rw [evaluate_expansion]
    calc
      (δ : ℝ) = ∑ k : Fin (n + 1), (δ : ℝ) * bernstein n k t := by
        rw [← Finset.mul_sum, bernstein.probability, mul_one]
      _ ≤ ∑ k : Fin (n + 1), (c k : ℝ) * bernstein n k t := by
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (Rat.cast_le.mpr (hc k)) bernstein_nonneg
  have h := congrArg (fun q ↦ evaluate q (t : ℝ)) heq
  rw [evaluate_compose, ht] at h
  exact (Rat.cast_pos.mpr hδ).trans_le (h ▸ hs)

end ADMM.UnitCircle.LowerCertificate
