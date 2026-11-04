/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_9.ch3_sec3_9_theorem_3_30

open scoped Matrix

-- Semantic search tool `lean_leansearch` was unavailable in this environment; this file reuses
-- the local Chapter 3 mixed equality/inequality API from Theorem 3.30 directly.

section Corollary_3_31

/-- Helper for Corollary 3.31: an equality certificate indexed by `Fin 0` contributes nothing to
the row/vector pair coming from Theorem 3.30. -/
lemma zero_equality_certificate_vanishes
    {n m : ℕ}
    (u : Fin 0 → ℝ)
    (lam : ℝ)
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (j : Fin m) :
    (lam • A j + u ᵥ* (0 : Matrix (Fin 0) (Fin n) ℝ),
        lam * b j + u ⬝ᵥ (0 : Fin 0 → ℝ)) =
      (lam • A j, lam * b j) := by
  -- Both certificate contributions are indexed by the empty type, so they simplify to zero.
  simp

/-- Corollary 3.31. Let `P` be a full-dimensional polyhedron and let `A *ᵥ x ≤ b` and
`C *ᵥ x ≤ d` be minimal representations of `P`. Then `A *ᵥ x ≤ b` is uniquely defined up to
multiplying inequalities by a positive scalar, equivalently up to permuting the rows and rescaling
each corresponding inequality by a positive scalar. -/
theorem full_dimensional_minimal_representation_unique_up_to_permutation_and_positive_scaling
    {n mA mC : ℕ}
    (P : Set (Fin n → ℝ))
    (A : Matrix (Fin mA) (Fin n) ℝ)
    (b : Fin mA → ℝ)
    (C : Matrix (Fin mC) (Fin n) ℝ)
    (d : Fin mC → ℝ)
    (hAmin :
      is_minimal_representation
        P
        (0 : Matrix (Fin 0) (Fin n) ℝ)
        (0 : Fin 0 → ℝ)
        A
        b)
    (hCmin :
      is_minimal_representation
        P
        (0 : Matrix (Fin 0) (Fin n) ℝ)
        (0 : Fin 0 → ℝ)
        C
        d) :
    ∃ σ : Fin mA ≃ Fin mC,
      ∀ j : Fin mA,
        ∃ lam : ℝ,
          0 < lam ∧
            (C (σ j), d (σ j)) = (lam • A j, lam * b j) := by
  -- Route correction: keep the theorem-3.30 skeleton and only erase the `Fin 0` equality
  -- certificate at the end, rather than hiding the specialization inside one global `simpa`.
  obtain ⟨σ, hσ⟩ :=
    minimal_representation_facet_rows_permutation_scaling_and_equalities
      P
      (0 : Matrix (Fin 0) (Fin n) ℝ)
      (0 : Fin 0 → ℝ)
      A
      b
      (0 : Matrix (Fin 0) (Fin n) ℝ)
      (0 : Fin 0 → ℝ)
      C
      d
      hAmin
      hCmin
  refine ⟨σ, ?_⟩
  intro j
  -- Each matched inequality row comes with a positive scalar and an equality-row certificate.
  obtain ⟨lam, hlam_pos, u, hu⟩ := hσ j
  refine ⟨lam, hlam_pos, ?_⟩
  -- The equality-row certificate vanishes because the pure-inequality specialization has no
  -- equality rows at all.
  calc
    (C (σ j), d (σ j)) =
        (lam • A j + u ᵥ* (0 : Matrix (Fin 0) (Fin n) ℝ),
          lam * b j + u ⬝ᵥ (0 : Fin 0 → ℝ)) := hu
    _ = (lam • A j, lam * b j) := zero_equality_certificate_vanishes u lam A b j

end Corollary_3_31
