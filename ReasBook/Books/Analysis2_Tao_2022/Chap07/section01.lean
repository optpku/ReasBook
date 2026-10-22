/-
Authors: Zichen Wang, Wanli Ma, Qiming Dai, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

section Chap07
section Section01

/-- Definition 7.1 (Measurable sets and Lebesgue measure axioms): for `n ∈ ℕ`, a collection
`M ⊆ 𝒫(ℝ^n)` and a function `m : M → [0, +∞]` (modeled here as
`m : Set (Fin n → ℝ) → ENNReal`) satisfy:
(i) every open set belongs to `M`;
(ii) `M` is closed under complements;
(iv) `M` is closed under countable unions and countable intersections;
(v) `m(∅) = 0`;
(vi) `0 ≤ m(Ω) ≤ +∞` for all `Ω ∈ M`;
(xi) countable additivity on pairwise disjoint measurable families;
(xii) `m([0,1]^n) = 1`;
(xiii) translation invariance: `x + Ω` is measurable and has the same measure. -/
def IsLebesgueMeasureAxioms (n : ℕ)
    (M : Set (Set (Fin n → ℝ))) (m : Set (Fin n → ℝ) → ENNReal) : Prop :=
  (∀ Ω : Set (Fin n → ℝ), IsOpen Ω → Ω ∈ M) ∧
    (∀ Ω : Set (Fin n → ℝ), Ω ∈ M → Ωᶜ ∈ M) ∧
      (∀ Ω : ℕ → Set (Fin n → ℝ), (∀ j : ℕ, Ω j ∈ M) → (⋃ j : ℕ, Ω j) ∈ M) ∧
        (∀ Ω : ℕ → Set (Fin n → ℝ), (∀ j : ℕ, Ω j ∈ M) → (⋂ j : ℕ, Ω j) ∈ M) ∧
          (m ∅ = 0) ∧
            (∀ Ω : Set (Fin n → ℝ), Ω ∈ M → 0 ≤ m Ω ∧ m Ω ≤ ⊤) ∧
              (∀ A : ℕ → Set (Fin n → ℝ),
                (∀ j : ℕ, A j ∈ M) →
                  Pairwise (fun i j : ℕ => Disjoint (A i) (A j)) →
                    m (⋃ j : ℕ, A j) = ∑' j : ℕ, m (A j)) ∧
                (m (Set.Icc (0 : Fin n → ℝ) 1) = 1) ∧
                  (∀ (Ω : Set (Fin n → ℝ)) (x : Fin n → ℝ),
                    Ω ∈ M →
                      (fun y : Fin n → ℝ => x + y) '' Ω ∈ M ∧
                        m ((fun y : Fin n → ℝ => x + y) '' Ω) = m Ω)

/-- Theorem 7.1 (Existence of Lebesgue measure): for each dimension `n`, there exist a
`σ`-algebra `M ⊆ 𝒫(ℝ^n)` and a function `m : M → [0,+∞]` (modeled as
`m : Set (Fin n → ℝ) → ENNReal`) satisfying the Borel property, complementarity,
closure under countable unions and intersections, `m(∅) = 0`, positivity,
countable additivity on pairwise disjoint families, normalization `m([0,1]^n) = 1`,
and translation invariance. -/
theorem exists_lebesgue_measure_axioms (n : ℕ) :
    ∃ (M : Set (Set (Fin n → ℝ))) (m : Set (Fin n → ℝ) → ENNReal),
      IsLebesgueMeasureAxioms n M m := by
  refine ⟨{ Ω : Set (Fin n → ℝ) | MeasurableSet Ω }, MeasureTheory.volume, ?_⟩
  constructor
  · intro Ω hΩ
    exact hΩ.measurableSet
  constructor
  · intro Ω hΩ
    simpa using (show MeasurableSet Ω from hΩ).compl
  constructor
  · intro Ω hΩ
    have hΩ' : ∀ j : ℕ, MeasurableSet (Ω j) := by
      intro j
      simpa using (hΩ j)
    exact MeasurableSet.iUnion hΩ'
  constructor
  · intro Ω hΩ
    have hΩ' : ∀ j : ℕ, MeasurableSet (Ω j) := by
      intro j
      simpa using (hΩ j)
    exact MeasurableSet.iInter hΩ'
  constructor
  · simp
  constructor
  · intro Ω hΩ
    exact ⟨bot_le, le_top⟩
  constructor
  · intro A hA hpair
    simpa [Function.onFun] using
      (MeasureTheory.measure_iUnion (μ := MeasureTheory.volume) (f := A) hpair hA)
  constructor
  · simpa using
      (Real.volume_Icc_pi (a := (0 : Fin n → ℝ)) (b := (1 : Fin n → ℝ)))
  · intro Ω x hΩ
    refine ⟨?_, ?_⟩
    · simpa [Set.image_add_left] using
        (show MeasurableSet Ω from hΩ).preimage (measurable_const_add (-x))
    · simp [Set.image_add_left]

end Section01
end Chap07
