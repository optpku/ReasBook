import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.RingTheory.Nullstellensatz

open scoped BigOperators
open MvPolynomial

variable {k : Type*} [Field k]

/-- A Nullstellensatz certificate is equivalent to saying that the given polynomials span the unit
ideal. -/
theorem nullstellensatz_certificate_iff_span_eq_top {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) :
    (∃ g : Fin m → MvPolynomial (Fin n) k, ∑ i, g i * f i = 1) ↔
      Ideal.span (Set.range f) = ⊤ := by
  rw [Ideal.eq_top_iff_one, Ideal.mem_span_range_iff_exists_fun]

/-- Theorem 10.17 (Hilbert's Nullstellensatz). For polynomials
`f : Fin m → MvPolynomial (Fin n) k` over a field `k`, the system `f i (x) = 0` has no
solution in `(AlgebraicClosure k)^n` if and only if there is a family of polynomials
`g : Fin m → MvPolynomial (Fin n) k` with `∑ i, g i * f i = 1`. -/
theorem hilbert_nullstellensatz_iff_no_common_root {n m : ℕ}
    (f : Fin m → MvPolynomial (Fin n) k) :
    (¬ ∃ x : Fin n → AlgebraicClosure k, ∀ i, aeval x (f i) = 0) ↔
      ∃ g : Fin m → MvPolynomial (Fin n) k, ∑ i, g i * f i = 1 := by
  classical
  rw [nullstellensatz_certificate_iff_span_eq_top]
  constructor
  · intro h
    by_contra hspan
    let I : Ideal (MvPolynomial (Fin n) k) := Ideal.span (Set.range f)
    have hspan' : I ≠ ⊤ := by
      simpa [I] using hspan
    have hzero : zeroLocus (AlgebraicClosure k) I ≠ ∅ := by
      intro hempty
      have hrad : I.radical = ⊤ := by
        calc
          I.radical = vanishingIdeal k (zeroLocus (AlgebraicClosure k) I) := by
            symm
            exact vanishingIdeal_zeroLocus_eq_radical I
          _ = ⊤ := by
            simpa [hempty] using
              (vanishingIdeal_empty :
                vanishingIdeal k (∅ : Set (Fin n → AlgebraicClosure k)) = ⊤)
      exact hspan' (Ideal.radical_eq_top.mp hrad)
    rcases Set.nonempty_iff_ne_empty.mpr hzero with ⟨x, hx⟩
    apply h
    refine ⟨x, ?_⟩
    rw [zeroLocus_span] at hx
    intro i
    exact hx (f i) ⟨i, rfl⟩
  · intro hcert hroot
    rcases hroot with ⟨x, hx⟩
    have hx' : x ∈ zeroLocus (AlgebraicClosure k) (Ideal.span (Set.range f)) := by
      rw [zeroLocus_span]
      intro p hp
      rcases hp with ⟨i, rfl⟩
      exact hx i
    have hx'' := hx'
    simp [hcert] at hx''
