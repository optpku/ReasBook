module

public import glowinski_admm_counterexample.ReasLib.ADMM.FiniteMemory.RationalReconstruction

@[expose] public section

namespace ADMM.FiniteMemory.Reconstruction

/-- A candidate LDL table satisfying the local rational recurrences has exactly
the pivots and strict lower entries produced by the existing fold evaluator.
No nonzero-pivot assumption is needed: both recurrences use total division. -/
theorem ldl_eq_of_recurrences {k : ℕ}
    (K L : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (D : (Fin k × Fin 2) → ℚ)
    (hD : ∀ i, D i = K i i - ∑ r : Fin k × Fin 2,
      if coordinateRank r < coordinateRank i then L i r ^ 2 * D r else 0)
    (hL : ∀ i j, coordinateRank i < coordinateRank j →
      L j i = (K j i - ∑ r : Fin k × Fin 2,
        if coordinateRank r < coordinateRank i then L j r * L i r * D r else 0) / D i) :
    (∀ i, (ldl K).pivot i = D i) ∧
      ∀ i j, coordinateRank i < coordinateRank j → (ldl K).lower j i = L j i := by
  have exactAt : ∀ n : ℕ, ∀ i : Fin k × Fin 2, coordinateRank i = n →
      (ldl K).pivot i = D i ∧
        ∀ j, coordinateRank i < coordinateRank j → (ldl K).lower j i = L j i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro i hi
      have previous (r : Fin k × Fin 2) (hr : coordinateRank r < coordinateRank i) :=
        ih (coordinateRank r) (by simpa only [hi] using hr) r rfl
      have pivot : (ldl K).pivot i = D i := by
        rw [ldl_pivot, hD i]
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        by_cases hr : coordinateRank r < coordinateRank i
        · simp only [hr, if_true]
          rw [(previous r hr).1, (previous r hr).2 i hr]
        · simp only [hr, if_false]
      refine ⟨pivot, ?_⟩
      intro j hij
      rw [ldl_lower K i j hij, pivot, hL i j hij]
      congr 2
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr : coordinateRank r < coordinateRank i
      · simp only [hr, if_true]
        rw [(previous r hr).1, (previous r hr).2 i hr,
          (previous r hr).2 j (hr.trans hij)]
      · simp only [hr, if_false]
  exact ⟨fun i ↦ (exactAt _ i rfl).1, fun i ↦ (exactAt _ i rfl).2⟩

/-- Check a candidate certificate by local identities and scalar positivity,
then recover the original recursive positive-pivot predicate. -/
theorem positivePivots_of_recurrences {k : ℕ}
    (K L : Matrix (Fin k × Fin 2) (Fin k × Fin 2) ℚ)
    (D : (Fin k × Fin 2) → ℚ) (threshold : ℚ)
    (hD : ∀ i, D i = K i i - ∑ r : Fin k × Fin 2,
      if coordinateRank r < coordinateRank i then L i r ^ 2 * D r else 0)
    (hL : ∀ i j, coordinateRank i < coordinateRank j →
      L j i = (K j i - ∑ r : Fin k × Fin 2,
        if coordinateRank r < coordinateRank i then L j r * L i r * D r else 0) / D i)
    (hpos : ∀ i, threshold < D i) : PositivePivots threshold K := by
  intro i
  rw [(ldl_eq_of_recurrences K L D hD hL).1 i]
  exact hpos i

end ADMM.FiniteMemory.Reconstruction
