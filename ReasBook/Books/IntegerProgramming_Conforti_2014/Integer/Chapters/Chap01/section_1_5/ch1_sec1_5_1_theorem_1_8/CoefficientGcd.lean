module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Int.GCD

@[expose] public section

open scoped BigOperators

variable {n : ℕ}

/-- The gcd of the coefficients of an integer row vector. -/
def coefficientGcd (a : Fin n → ℤ) : ℤ :=
  Finset.univ.gcd a

/-- Helper for Theorem 1.8: adjoining one head coordinate identifies the coefficient gcd with the
gcd of the new head entry and the old tail coefficient gcd. -/
theorem coefficientGcd_cons (x : ℤ) (xs : Fin n → ℤ) :
    coefficientGcd (Fin.cons x xs) = (Int.gcd x (coefficientGcd xs) : ℤ) := by
  -- Route correction: keep the head-tail gcd normalization at the coefficient-gcd owner so both
  -- the support Bézout proof and the main theorem reuse the same canonical statement.
  have huniv :
      (Finset.univ : Finset (Fin (n + 1))) = insert 0 (Finset.univ.image Fin.succ) := by
    ext i
    cases i using Fin.cases <;> simp
  -- Rewrite the `Fin (n + 1)` index set into the new head and the old tail image.
  rw [coefficientGcd, huniv, Finset.gcd_insert, Finset.gcd_image, coefficientGcd]
  simpa using (Int.coe_gcd x (coefficientGcd xs)).symm

/-- Every coefficient of an integer row vector is divisible by `coefficientGcd a`. -/
theorem coefficientGcd_dvd (a : Fin n → ℤ) (i : Fin n) :
    coefficientGcd a ∣ a i := by
  -- Unfold the coefficient gcd and apply the finset divisibility lemma at the chosen index.
  rw [coefficientGcd]
  exact Finset.gcd_dvd (by simp)

/-- Helper for Theorem 1.8: a Bézout witness for the tail extends to one for a new head
coordinate by the binary extended gcd coefficients. -/
lemma exists_sum_mul_eq_coefficientGcd_cons
    (x : ℤ)
    (xs : Fin n → ℤ)
    (u : Fin n → ℤ)
    (hu : (∑ i : Fin n, xs i * u i) = coefficientGcd xs) :
    ∃ v : Fin (n + 1) → ℤ, (∑ i : Fin (n + 1), ((Fin.cons x xs : Fin (n + 1) → ℤ) i) * v i) =
      coefficientGcd (Fin.cons x xs) := by
  let v : Fin (n + 1) → ℤ :=
    Fin.cons (Int.gcdA x (coefficientGcd xs))
      (fun i ↦ Int.gcdB x (coefficientGcd xs) * u i)
  refine ⟨v, ?_⟩
  -- Split the head term from the tail sum and then factor the common `gcdB` coefficient.
  calc
    (∑ i : Fin (n + 1),
        ((Fin.cons x xs : Fin (n + 1) → ℤ) i) * v i) =
          x * Int.gcdA x (coefficientGcd xs) +
            ∑ i : Fin n, xs i * (Int.gcdB x (coefficientGcd xs) * u i) := by
              rw [Fin.sum_univ_succ]
              simp [v]
    _ =
          x * Int.gcdA x (coefficientGcd xs) +
            Int.gcdB x (coefficientGcd xs) * ∑ i : Fin n, xs i * u i := by
              congr 1
              calc
                ∑ i : Fin n, xs i * (Int.gcdB x (coefficientGcd xs) * u i)
                    =
                      ∑ i : Fin n, Int.gcdB x (coefficientGcd xs) * (xs i * u i) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        simpa [mul_assoc, mul_left_comm, mul_comm]
                _ = Int.gcdB x (coefficientGcd xs) * ∑ i : Fin n, xs i * u i := by
                      rw [Finset.mul_sum]
    _ =
          x * Int.gcdA x (coefficientGcd xs) +
            Int.gcdB x (coefficientGcd xs) * coefficientGcd xs := by
              rw [hu]
    _ = coefficientGcd (Fin.cons x xs) := by
          rw [coefficientGcd_cons, Int.gcd_eq_gcd_ab]

/-- The coefficient gcd is an integer linear combination of the coefficients. -/
theorem exists_sum_mul_eq_coefficientGcd (a : Fin n → ℤ) :
    ∃ u : Fin n → ℤ, (∑ i : Fin n, a i * u i) = coefficientGcd a := by
  induction n with
  | zero =>
      refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
      -- The empty sum and empty gcd both vanish in dimension zero.
      simp [coefficientGcd]
  | succ n ih =>
      rcases ih (Fin.tail a) with ⟨u, hu⟩
      rcases exists_sum_mul_eq_coefficientGcd_cons (a 0) (Fin.tail a) u hu with ⟨v, hv⟩
      -- Decompose the vector into its head and tail, then reuse the successor-step witness.
      refine ⟨v, ?_⟩
      simpa [Fin.cons_self_tail] using hv

/-- A nonzero integer row vector has nonzero coefficient gcd. -/
theorem coefficientGcd_ne_zero_of_nonzero (a : Fin n → ℤ) (ha : a ≠ 0) :
    coefficientGcd a ≠ 0 := by
  intro hg
  -- If the coefficient gcd vanished, every coordinate would vanish as well, forcing `a = 0`.
  rw [coefficientGcd, Finset.gcd_eq_zero_iff] at hg
  apply ha
  funext i
  exact hg i (by simp)

end
