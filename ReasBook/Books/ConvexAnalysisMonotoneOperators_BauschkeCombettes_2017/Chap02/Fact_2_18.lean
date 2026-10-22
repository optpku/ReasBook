/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix OrderDual Tuple

-- Private helper: an antitone permutation of `x`.
private def IsAntitonePerm {N : ℕ} (x xDown : Fin N → ℝ) : Prop :=
  Antitone xDown ∧ ∃ σ : Equiv.Perm (Fin N), xDown = x ∘ σ

/-- The canonical nonincreasing rearrangement of a finite real vector, obtained by sorting it in
descending order. -/
noncomputable def nonincreasingRearrangement {N : ℕ} (x : Fin N → ℝ) : Fin N → ℝ :=
  x ∘ sort (toDual ∘ x)

/-- The canonical nonincreasing rearrangement is antitone. -/
theorem antitone_nonincreasingRearrangement
    {N : ℕ} (x : Fin N → ℝ) :
    Antitone (nonincreasingRearrangement x) := by
  simpa [nonincreasingRearrangement, Function.comp_assoc] using
    (monotone_sort (toDual ∘ x) : Monotone ((toDual ∘ x) ∘ sort (toDual ∘ x)))

-- The canonical sorted tuple is an antitone permutation of the original tuple.
private theorem isAntitonePerm_nonincreasingRearrangement
    {N : ℕ} (x : Fin N → ℝ) :
    IsAntitonePerm x (nonincreasingRearrangement x) := by
  refine ⟨antitone_nonincreasingRearrangement x, sort (toDual ∘ x), rfl⟩

-- Helper for Fact 2.18: rewrite the original dot product through the sorting permutations.
private lemma dotProduct_eq_sorted_dotProduct_comp_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    {σx σy : Equiv.Perm (Fin N)}
    (hxEq : xDown = x ∘ σx) (hyEq : yDown = y ∘ σy) :
    dotProduct x y = dotProduct xDown (yDown ∘ (σx.trans σy.symm)) := by
  have hyComp : y ∘ σx = yDown ∘ (σx.trans σy.symm) := by
    funext i
    simp [hyEq]
  -- Move both vectors through the sorting permutation of `x`, then identify the induced
  -- permutation on the sorted version of `y`.
  calc
    dotProduct x y = dotProduct (x ∘ σx) (y ∘ σx) := by
      simp
    _ = dotProduct xDown (y ∘ σx) := by
      simp [hxEq]
    _ = dotProduct xDown (yDown ∘ (σx.trans σy.symm)) := by
      simp [hyComp]

-- Helper for Fact 2.18: if the sorted `y`-vector composed with a permutation still monovaries
-- with the sorted `x`-vector, then one can reorder only inside equal-value blocks of `xDown` to
-- recover `yDown`.
private theorem exists_block_preserving_perm_of_monovary_sorted_comp
    {N : ℕ} {xDown yDown : Fin N → ℝ}
    (hxAnti : Antitone xDown) (hyAnti : Antitone yDown)
    (τ : Equiv.Perm (Fin N))
    (hmono : Monovary xDown (yDown ∘ τ)) :
    ∃ ρ : Equiv.Perm (Fin N), xDown ∘ ρ = xDown ∧ yDown ∘ τ ∘ ρ = yDown := by
  classical
  obtain ⟨auxOrder, hxAux, hyAux⟩ := hmono.exists_antitone
  have e : @OrderIso (Fin N) (Fin N) instLEFin auxOrder.toLE := by
    letI := auxOrder
    exact monoEquivOfFin (Fin N) (Fintype.card_fin N)
  let ρ : Equiv.Perm (Fin N) := e.toEquiv
  -- Transport the auxiliary antitone order back to the standard order on `Fin N`.
  have hxComp : Antitone (xDown ∘ ρ) := by
    intro i j hij
    have hij' : @LE.le (Fin N) auxOrder.toLE (ρ i) (ρ j) := by
      change @LE.le (Fin N) auxOrder.toLE (e i) (e j)
      exact e.map_rel_iff'.2 hij
    exact hxAux hij'
  have hyComp : Antitone (yDown ∘ (ρ.trans τ)) := by
    intro i j hij
    have hij' : @LE.le (Fin N) auxOrder.toLE (ρ i) (ρ j) := by
      change @LE.le (Fin N) auxOrder.toLE (e i) (e j)
      exact e.map_rel_iff'.2 hij
    simpa [ρ] using hyAux hij'
  refine ⟨ρ, ?_, ?_⟩
  · -- The sorted tuple `xDown` is the unique antitone permutation of itself.
    have hxEq : xDown ∘ ρ = xDown ∘ Equiv.refl (Fin N) := unique_antitone hxComp (by simpa using hxAnti)
    simpa using hxEq
  · -- The same uniqueness argument forces the transported `yDown` tuple back to `yDown`.
    have hyEq : yDown ∘ (ρ.trans τ) = yDown ∘ Equiv.refl (Fin N) :=
      unique_antitone hyComp (by simpa using hyAnti)
    simpa [Function.comp_assoc] using hyEq

-- Proof sketch: choose permutations sending `x` and `y` to `xDown` and `yDown`, apply mathlib's
-- rearrangement inequality to the antitone rearrangements.
/-- Fact 2.18: the Euclidean inner product of two finite real vectors is bounded above by the inner
product of their nonincreasing rearrangements. -/
private theorem hardy_littlewood_polya_inequality_of_antitone_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    (hxDown : IsAntitonePerm x xDown)
    (hyDown : IsAntitonePerm y yDown) :
    dotProduct x y ≤ dotProduct xDown yDown := by
  rcases hxDown with ⟨hxAnti, σx, hxEq⟩
  rcases hyDown with ⟨hyAnti, σy, hyEq⟩
  let τ : Equiv.Perm (Fin N) := σx.trans σy.symm
  have hmono : Monovary xDown yDown := Antitone.monovary hxAnti hyAnti
  have hineq : dotProduct xDown (yDown ∘ τ) ≤ dotProduct xDown yDown := by
    have hineq' : ∑ i, xDown i * yDown (τ i) ≤ ∑ i, xDown i * yDown i :=
      hmono.sum_mul_comp_perm_le_sum_mul
    simpa [dotProduct, τ] using hineq'
  -- Rewrite the original inner product into the rearrangement form and apply mathlib's inequality.
  calc
    dotProduct x y = dotProduct xDown (yDown ∘ τ) := by
      simpa [τ] using dotProduct_eq_sorted_dotProduct_comp_perm hxEq hyEq
    _ ≤ dotProduct xDown yDown := hineq

-- Proof sketch: combine the rearrangement equality case with the uniqueness of antitone
-- rearrangements to identify equality with the existence of a common sorting permutation.
/-- Equality in the Hardy-Littlewood-Polya inequality holds exactly when one permutation sends both
vectors to their nonincreasing rearrangements. -/
private theorem hardy_littlewood_polya_inequality_eq_iff_of_antitone_perm
    {N : ℕ} {x y xDown yDown : Fin N → ℝ}
    (hxDown : IsAntitonePerm x xDown)
    (hyDown : IsAntitonePerm y yDown) :
    dotProduct x y = dotProduct xDown yDown ↔
      ∃ σ : Equiv.Perm (Fin N),
        xDown = x ∘ σ ∧ yDown = y ∘ σ := by
  rcases hxDown with ⟨hxAnti, σx, hxEq⟩
  rcases hyDown with ⟨hyAnti, σy, hyEq⟩
  let τ : Equiv.Perm (Fin N) := σx.trans σy.symm
  constructor
  · intro hEq
    have hrewrite : dotProduct x y = dotProduct xDown (yDown ∘ τ) := by
      simpa [τ] using dotProduct_eq_sorted_dotProduct_comp_perm hxEq hyEq
    have hSortedEq : dotProduct xDown (yDown ∘ τ) = dotProduct xDown yDown := by
      rw [← hrewrite]
      exact hEq
    have hmono : Monovary xDown (yDown ∘ τ) := by
      have hxy : Monovary xDown yDown := Antitone.monovary hxAnti hyAnti
      have hSortedEq' : ∑ i, xDown i * yDown (τ i) = ∑ i, xDown i * yDown i := by
        simpa [dotProduct, τ] using hSortedEq
      exact (hxy.sum_mul_comp_perm_eq_sum_mul_iff).mp hSortedEq'
    obtain ⟨ρ, hxPres, hyPres⟩ :=
      exists_block_preserving_perm_of_monovary_sorted_comp hxAnti hyAnti τ hmono
    refine ⟨ρ.trans σx, ?_, ?_⟩
    · calc
        xDown = xDown ∘ ρ := hxPres.symm
        _ = x ∘ (ρ.trans σx) := by
          funext i
          simp [hxEq]
    · calc
        yDown = yDown ∘ τ ∘ ρ := hyPres.symm
        _ = y ∘ (ρ.trans σx) := by
          funext i
          simp [τ, hyEq, Function.comp_assoc]
  · rintro ⟨σ, hxPerm, hyPerm⟩
    -- A common permutation preserves the dot product, so the sorted and unsorted products agree.
    calc
      dotProduct x y = dotProduct (x ∘ σ) (y ∘ σ) := by
        simp
      _ = dotProduct xDown yDown := by
        simp [hxPerm, hyPerm]

/-- Fact 2.18: the Euclidean inner product of two finite real vectors is bounded above by the inner
product of their canonical nonincreasing rearrangements. -/
theorem hardy_littlewood_polya_inequality
    {N : ℕ} {x y : Fin N → ℝ} :
    dotProduct x y ≤
      dotProduct (nonincreasingRearrangement x) (nonincreasingRearrangement y) := by
  simpa using
    hardy_littlewood_polya_inequality_of_antitone_perm
      (isAntitonePerm_nonincreasingRearrangement x)
      (isAntitonePerm_nonincreasingRearrangement y)

/- Equality in Fact 2.18 says that the same permutation sorts both vectors into descending order. -/
theorem hardy_littlewood_polya_inequality_eq_iff
    {N : ℕ} {x y : Fin N → ℝ} :
    dotProduct x y =
        dotProduct (nonincreasingRearrangement x) (nonincreasingRearrangement y) ↔
      ∃ σ : Equiv.Perm (Fin N),
        nonincreasingRearrangement x = x ∘ σ ∧
          nonincreasingRearrangement y = y ∘ σ := by
  simpa using
    hardy_littlewood_polya_inequality_eq_iff_of_antitone_perm
      (isAntitonePerm_nonincreasingRearrangement x)
      (isAntitonePerm_nonincreasingRearrangement y)
