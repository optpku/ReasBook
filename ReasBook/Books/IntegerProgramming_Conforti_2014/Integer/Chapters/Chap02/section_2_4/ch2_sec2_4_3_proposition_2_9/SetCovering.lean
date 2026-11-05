/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_3_definition_2_16.Blocker
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Notation.Support
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Defs

open scoped BigOperators

public section

namespace SetTransversal

section SetCovering

variable {α : Type}

/-- The characteristic vector `χ_s` of a finite subset `s` of the ground set. -/
def characteristicVector [DecidableEq α] (s : Finset α) : α → ℤ :=
  fun e ↦ if e ∈ s then 1 else 0

namespace SetCoveringNotation

/-- Lean surface for the textbook characteristic vector `χ_s`, written as `χ_{s}`. -/
scoped macro:max "χ_{" s:term "}" : term =>
  `(characteristicVector $s)

end SetCoveringNotation

open scoped SetCoveringNotation

/-- The support of the characteristic vector `χ_s` is exactly `s`, viewed canonically as a set. -/
theorem support_characteristicVector [DecidableEq α] (s : Finset α) :
    Function.support (χ_{s}) = (s : Set α) := by
  ext e
  simp [characteristicVector, Function.mem_support]

/-- A member `x` of a family of vectors is minimal for support inclusion when every competing
member whose support is contained in the support of `x` has the same support. -/
def IsMinimalSupportMember (X : Set (α → ℤ)) (x : α → ℤ) : Prop :=
  x ∈ X ∧
    ∀ ⦃y : α → ℤ⦄,
      y ∈ X →
        Function.support y ⊆ Function.support x →
          Function.support x ⊆ Function.support y

/-- Unfolding specification for `IsMinimalSupportMember`. -/
theorem isMinimalSupportMember_iff
    {X : Set (α → ℤ)} {x : α → ℤ} :
    IsMinimalSupportMember X x ↔
      x ∈ X ∧
        ∀ ⦃y : α → ℤ⦄,
          y ∈ X →
            Function.support y ⊆ Function.support x →
              Function.support x ⊆ Function.support y :=
  Iff.rfl

section FiniteGround

variable {n : ℕ}

/-- The source-facing covering family `S^C(incidenceMatrix T)` attached to the incidence-matrix
presentation of `T`. -/
def incidenceSetCoveringFamily (T : Finset (Finset (Fin n))) : Set (Fin n → ℤ) :=
  {x | (∀ e, x e = 0 ∨ x e = 1) ∧ ∀ t ∈ T, 1 ≤ t.sum x}

/-- Membership in `S^C(incidenceMatrix T)` is exactly the binary condition together with the
covering inequalities indexed by the members of `T`. -/
theorem mem_incidenceSetCoveringFamily_iff
    {T : Finset (Finset (Fin n))} {x : Fin n → ℤ} :
    x ∈ incidenceSetCoveringFamily T ↔
      (∀ e, x e = 0 ∨ x e = 1) ∧ ∀ t ∈ T, 1 ≤ t.sum x :=
  Iff.rfl

namespace SetCoveringNotation

/-- Lean surface for the textbook notation `S^C(incidenceMatrix T)`. -/
scoped macro:max "S^C(incidenceMatrix " T:term ")" : term =>
  `(incidenceSetCoveringFamily $T)

end SetCoveringNotation

open scoped SetCoveringNotation

/-- Helper for Proposition 2.9: the support filter on `Finset.univ` is exactly `Function.support`
for a vector on `Fin n`. -/
theorem supportFilter_eq_support (x : Fin n → ℤ) :
    ((Finset.univ.filter fun e ↦ x e ≠ 0 : Finset (Fin n)) : Set (Fin n)) =
      Function.support x := by
  -- On a finite ground set, support is just the filter of nonzero coordinates.
  ext e
  simp [Function.mem_support]

/-- Helper for Proposition 2.9: a binary integer-valued vector is pointwise nonnegative. -/
theorem binary_nonneg
    {x : Fin n → ℤ} (hx01 : ∀ e, x e = 0 ∨ x e = 1) :
    ∀ e, 0 ≤ x e := by
  intro e
  rcases hx01 e with h0 | h1
  · simp [h0]
  · simp [h1]

/-- Helper for Proposition 2.9: for a binary vector, the covering inequality on a row `t` is
equivalent to the support of `x` meeting `t`. -/
theorem one_le_sum_iff_supportInter_nonempty
    {t : Finset (Fin n)} {x : Fin n → ℤ}
    (hx01 : ∀ e, x e = 0 ∨ x e = 1) :
    1 ≤ t.sum x ↔ (Function.support x ∩ (t : Set (Fin n))).Nonempty := by
  classical
  constructor
  · intro hsum
    -- If no support point lies on `t`, then every term in the row sum vanishes.
    by_contra hEmpty
    have hZero : ∀ e ∈ t, x e = 0 := by
      intro e he
      by_contra hxne
      exact hEmpty ⟨e, hxne, he⟩
    have hsumZero : t.sum x = 0 := by
      refine Finset.sum_eq_zero ?_
      intro e he
      exact hZero e he
    have hFalse : ¬ ((1 : ℤ) ≤ 0) := by
      decide
    have hOneLeZero : (1 : ℤ) ≤ 0 := by
      rwa [hsumZero] at hsum
    exact hFalse hOneLeZero
  · rintro ⟨e, heSupport, heMem⟩
    have hxe : x e = 1 := by
      rcases hx01 e with h0 | h1
      · exact False.elim (heSupport h0)
      · exact h1
    -- A support witness contributes at least `1` to the row sum,
    -- and all other terms are nonnegative.
    have hSingle :
        x e ≤ t.sum x := by
      exact Finset.single_le_sum (fun i hi ↦ binary_nonneg hx01 i) heMem
    simpa [hxe] using hSingle

/-- Helper for Proposition 2.9: the support filter of a vector is a transversal exactly when the
support of the vector meets every member of `T`. -/
theorem supportFilter_isTransversal_of_hits
    {T : Finset (Finset (Fin n))} {x : Fin n → ℤ}
    (hxHits : ∀ t ∈ T, (Function.support x ∩ (t : Set (Fin n))).Nonempty) :
    Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n)))
      (Finset.univ.filter fun e ↦ x e ≠ 0) := by
  refine Clutter.IsTransversal.ofSubsetGroundAndHits (Finset.filter_subset _ _) ?_
  intro t ht
  rcases hxHits t ht with ⟨e, heSupport, heMem⟩
  -- A support witness for `x` becomes a concrete point of the filtered transversal.
  refine ⟨e, ?_⟩
  rw [Finset.mem_inter]
  exact ⟨heMem, by simpa [Function.mem_support] using heSupport⟩

/-- Helper for Proposition 2.9: a binary vector is exactly the characteristic vector of its
support filter. -/
theorem eq_characteristicVector_supportFilter_of_binary
    {x : Fin n → ℤ} (hx01 : ∀ e, x e = 0 ∨ x e = 1) :
    x = χ_{Finset.univ.filter fun e ↦ x e ≠ 0} := by
  -- Each coordinate is either the zero branch or the one branch of the characteristic vector.
  funext e
  by_cases hx0 : x e = 0
  · have heNotMem : e ∉ Finset.univ.filter fun a ↦ x a ≠ 0 := by
      simp [hx0]
    simp [characteristicVector, heNotMem, hx0]
  · have hxe : x e = 1 := by
      rcases hx01 e with h0 | h1
      · exact False.elim (hx0 h0)
      · exact h1
    have heMem : e ∈ Finset.univ.filter fun a ↦ x a ≠ 0 := by
      simp [hx0]
    simp [characteristicVector, heMem, hxe]

/-- For the incidence matrix of `T`, membership in `S^C(incidenceMatrix T)` is exactly the
condition that `x` is binary and that its support meets every member of `T`. -/
theorem mem_setCoveringFamily_incidenceMatrix_iff
    {T : Finset (Finset (Fin n))} {x : Fin n → ℤ} :
    x ∈ S^C(incidenceMatrix T) ↔
      (∀ e, x e = 0 ∨ x e = 1) ∧
        ∀ t ∈ T, (Function.support x ∩ (t : Set (Fin n))).Nonempty := by
  constructor
  · intro hx
    rw [mem_incidenceSetCoveringFamily_iff] at hx
    rcases hx with ⟨hx01, hxCover⟩
    refine ⟨hx01, ?_⟩
    intro t ht
    -- Rewrite each covering inequality into the support-hitting condition on `t`.
    exact (one_le_sum_iff_supportInter_nonempty hx01).mp (hxCover t ht)
  · rintro ⟨hx01, hxHits⟩
    rw [mem_incidenceSetCoveringFamily_iff]
    refine ⟨hx01, ?_⟩
    intro t ht
    -- The support-hitting condition on `t` is exactly the row inequality for binary vectors.
    exact (one_le_sum_iff_supportInter_nonempty hx01).mpr (hxHits t ht)

/-- Helper for Proposition 2.9: the characteristic vector of a transversal of `T` lies in
`S^C(incidenceMatrix T)`. -/
theorem characteristicVector_mem_setCoveringFamily_of_transversal
    {T : Finset (Finset (Fin n))} {s : Finset (Fin n)}
    (hs : Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n))) s) :
    χ_{s} ∈ S^C(incidenceMatrix T) := by
  refine (mem_setCoveringFamily_incidenceMatrix_iff).mpr ?_
  refine ⟨?_, ?_⟩
  · intro e
    by_cases he : e ∈ s
    · right
      simp [characteristicVector, he]
    · left
      simp [characteristicVector, he]
  · intro t ht
    rcases hs.hits t ht with ⟨e, he⟩
    refine ⟨e, ?_⟩
    refine ⟨?_, Finset.mem_of_mem_inter_left he⟩
    -- A point of `s` is exactly a point of the support of `χ_s`.
    simpa [support_characteristicVector] using Finset.mem_of_mem_inter_right he

/-- For the incidence matrix of a finite family `T` on `Fin n`, the minimal-support members of
`S^C(incidenceMatrix T)` are exactly the characteristic vectors `χ_s` of the members of the
blocker of `T`. -/
theorem isMinimalSupportMember_setCoveringFamily_incidenceMatrix_iff_mem_blocker
    {T : Finset (Finset (Fin n))} {x : Fin n → ℤ} :
    IsMinimalSupportMember (S^C(incidenceMatrix T)) x ↔
      ∃ s ∈ Clutter.blocker Finset.univ (T : Set (Finset (Fin n))),
        x = χ_{s} := by
  constructor
  · intro hxMin
    rcases (isMinimalSupportMember_iff.mp hxMin) with ⟨hxMem, hxMinimal⟩
    rcases (mem_setCoveringFamily_incidenceMatrix_iff.mp hxMem) with ⟨hx01, hxHits⟩
    let u : Finset (Fin n) := Finset.univ.filter fun e ↦ x e ≠ 0
    have huTrans :
        Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n))) u := by
      -- The support-hitting description makes the filtered support into a transversal.
      exact supportFilter_isTransversal_of_hits hxHits
    have huBlocker :
        u ∈ Clutter.blocker Finset.univ (T : Set (Finset (Fin n))) := by
      refine Clutter.mem_blocker_iff.mpr ?_
      refine ⟨huTrans, ?_⟩
      intro v hvTrans hvSubset
      have hvMem :
          χ_{v} ∈ S^C(incidenceMatrix T) :=
        characteristicVector_mem_setCoveringFamily_of_transversal hvTrans
      have hvSupportSubset :
          Function.support (χ_{v}) ⊆ Function.support x := by
        -- A smaller transversal gives a competitor with smaller support.
        intro e he
        have heV : e ∈ v := by
          simpa [support_characteristicVector] using he
        have heU : e ∈ u := hvSubset heV
        simpa [u, supportFilter_eq_support] using heU
      have hxSupportSubset :
          Function.support x ⊆ Function.support (χ_{v}) :=
        hxMinimal hvMem hvSupportSubset
      -- Minimality of `x` forces its support to be contained in every transversal competitor.
      intro e he
      have heSupport : e ∈ Function.support x := by
        simpa [u, supportFilter_eq_support] using he
      have heVSupport : e ∈ Function.support (χ_{v}) := hxSupportSubset heSupport
      simpa [support_characteristicVector] using heVSupport
    refine ⟨u, huBlocker, ?_⟩
    -- A binary vector is the characteristic vector of its support filter.
    simpa [u] using eq_characteristicVector_supportFilter_of_binary hx01
  · rintro ⟨s, hsBlocker, rfl⟩
    have hsMin :
        Minimal
          (fun u ↦ Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n))) u)
          s :=
      Clutter.mem_blocker_iff.mp hsBlocker
    refine (isMinimalSupportMember_iff).mpr ?_
    refine ⟨characteristicVector_mem_setCoveringFamily_of_transversal hsMin.prop, ?_⟩
    intro y hyMem hySupportSubset
    rcases (mem_setCoveringFamily_incidenceMatrix_iff.mp hyMem) with ⟨hy01, hyHits⟩
    let u : Finset (Fin n) := Finset.univ.filter fun e ↦ y e ≠ 0
    have huTrans :
        Clutter.IsTransversal Finset.univ (T : Set (Finset (Fin n))) u := by
      -- Any competing covering vector again yields a transversal through its support filter.
      exact supportFilter_isTransversal_of_hits hyHits
    have huSubset :
        u ⊆ s := by
      -- Support inclusion translates directly into filtered-support inclusion.
      intro e he
      have heSupport : e ∈ Function.support y := by
        simpa [u, supportFilter_eq_support] using he
      have heChi : e ∈ Function.support (χ_{s}) := hySupportSubset heSupport
      simpa [support_characteristicVector] using heChi
    have hsSubset :
        s ⊆ u := hsMin.le_of_le huTrans huSubset
    -- The blocker minimality of `s` upgrades the competitor support inclusion
    -- to equality of supports.
    intro e he
    have heS : e ∈ s := by
      simpa [support_characteristicVector] using he
    have heU : e ∈ u := hsSubset heS
    simpa [u, supportFilter_eq_support] using heU

end FiniteGround

end SetCovering

end SetTransversal
