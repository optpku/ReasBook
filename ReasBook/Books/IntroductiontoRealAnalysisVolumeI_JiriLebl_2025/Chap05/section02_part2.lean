/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section02_part1

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02
/-- Lemma 5.2.1: If `a < b < c` and `f : [a, c] → ℝ` is bounded, then the
lower and upper Darboux integrals over `[a, c]` split as the sums of the
integrals over `[a, b]` and `[b, c]`. That is,
`∫̲_a^c f = ∫̲_a^b f + ∫̲_b^c f` and `∫̅_a^c f = ∫̅_a^b f + ∫̅_b^c f`. -/
lemma darbouxIntegral_add {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hbc : b < c)
    (hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M) :
    lowerDarbouxIntegral f a c =
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c ∧
      upperDarbouxIntegral f a c =
        upperDarbouxIntegral f a b + upperDarbouxIntegral f b c := by
  classical
  rcases hbound with ⟨M, hM⟩
  have hbound' : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M := ⟨M, hM⟩
  have hmin : ∀ x ∈ Set.Icc a c, -M ≤ f x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a c, f x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  have hbound_ab : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
    refine ⟨M, ?_⟩
    intro x hx
    exact hM x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
  have hbound_bc : ∃ M : ℝ, ∀ x ∈ Set.Icc b c, |f x| ≤ M := by
    refine ⟨M, ?_⟩
    intro x hx
    exact hM x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
  constructor
  · have hrestrict :=
      (darbouxIntegral_restrict_to_partitions_with_point (a := a) (b := b) (c := c)
        (f := f) hab hbc hbound').1
    have hmin_ab : ∀ x ∈ Set.Icc a b, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
    have hmax_ab : ∀ x ∈ Set.Icc a b, f x ≤ M := by
      intro x hx
      exact hmax x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
    have hmin_bc : ∀ x ∈ Set.Icc b c, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
    have hmax_bc : ∀ x ∈ Set.Icc b c, f x ≤ M := by
      intro x hx
      exact hmax x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
    have hBddAbove_ab :
        BddAbove (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
      refine ⟨M * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := -M) (M := M) hmin_ab hmax_ab P
      exact le_trans hsum.2.1 hsum.2.2
    have hBddAbove_bc :
        BddAbove (Set.range (fun P : IntervalPartition b c => lowerDarbouxSum f P)) := by
      refine ⟨M * (c - b), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := b) (b := c) (m := -M) (M := M) hmin_bc hmax_bc P
      exact le_trans hsum.2.1 hsum.2.2
    have hS_nonempty :
        (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            lowerDarbouxSum f P.1)).Nonempty := by
      rcases intervalPartition_three_points (a := a) (b := b) (c := c) hab hbc with ⟨P0, hbP0⟩
      refine ⟨lowerDarbouxSum f P0, ?_⟩
      exact ⟨⟨P0, hbP0⟩, rfl⟩
    have hle :
        sSup (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            lowerDarbouxSum f P.1)) ≤
          lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c := by
      refine csSup_le hS_nonempty ?_
      intro y hy
      rcases hy with ⟨P, rfl⟩
      rcases intervalPartition_split_at_point (f := f) (P := P.1) P.2 with
        ⟨P1, P2, hsum_lower, _⟩
      have hle1 : lowerDarbouxSum f P1 ≤ lowerDarbouxIntegral f a b := by
        have hsup := le_csSup hBddAbove_ab (by exact ⟨P1, rfl⟩)
        simpa [lowerDarbouxIntegral] using hsup
      have hle2 : lowerDarbouxSum f P2 ≤ lowerDarbouxIntegral f b c := by
        have hsup := le_csSup hBddAbove_bc (by exact ⟨P2, rfl⟩)
        simpa [lowerDarbouxIntegral] using hsup
      calc
        lowerDarbouxSum f P.1 =
            lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := hsum_lower
        _ ≤ lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c := add_le_add hle1 hle2
    have hle' : lowerDarbouxIntegral f a c ≤
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c := by
      simpa [hrestrict] using hle
    refine le_antisymm hle' ?_
    have hnonempty_ab :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) (le_of_lt hab)
      refine ⟨lowerDarbouxSum f P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hnonempty_bc :
        (Set.range (fun P : IntervalPartition b c => lowerDarbouxSum f P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := b) (b := c) (le_of_lt hbc)
      refine ⟨lowerDarbouxSum f P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hBddAbove_S :
        BddAbove (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            lowerDarbouxSum f P.1)) := by
      refine ⟨M * (c - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P.1
      exact le_trans hsum.2.1 hsum.2.2
    by_contra hlt
    set S := Set.range (fun P :
      {P : IntervalPartition a c // b ∈ Set.range P.points} =>
        lowerDarbouxSum f P.1)
    set A : ℝ := lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c
    set B : ℝ := sSup S
    have hlt' : B < A := by
      have hlt'' : lowerDarbouxIntegral f a c < A := lt_of_not_ge hlt
      simpa [A, B, S, hrestrict] using hlt''
    set ε : ℝ := (A - B) / 2
    have hεpos : 0 < ε := by
      have hεpos' : 0 < (A - B) / 2 := by linarith [hlt']
      simpa [ε] using hεpos'
    have hlt1 :
        lowerDarbouxIntegral f a b - ε / 2 <
          sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f P)) := by
      have hlt1' : lowerDarbouxIntegral f a b - ε / 2 < lowerDarbouxIntegral f a b := by
        linarith [hεpos]
      simpa [lowerDarbouxIntegral] using hlt1'
    obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_lt_csSup hnonempty_ab hlt1
    have hlt2 :
        lowerDarbouxIntegral f b c - ε / 2 <
          sSup (Set.range (fun P : IntervalPartition b c => lowerDarbouxSum f P)) := by
      have hlt2' : lowerDarbouxIntegral f b c - ε / 2 < lowerDarbouxIntegral f b c := by
        linarith [hεpos]
      simpa [lowerDarbouxIntegral] using hlt2'
    obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_lt_csSup hnonempty_bc hlt2
    rcases intervalPartition_append (f := f) P1 P2 with ⟨P, hbP, hsum_lower, _⟩
    have hsum_gt : A - ε < lowerDarbouxSum f P := by
      have hsum_gt' :
          A - ε < lowerDarbouxSum f P1 + lowerDarbouxSum f P2 := by
        linarith [hP1, hP2]
      simpa [hsum_lower] using hsum_gt'
    have hmem : lowerDarbouxSum f P ∈ S := by
      exact ⟨⟨P, hbP⟩, rfl⟩
    have hle_sup : lowerDarbouxSum f P ≤ B := by
      have hle' := le_csSup hBddAbove_S hmem
      simpa [B] using hle'
    have hgt : B < A - ε := by
      have hgt' : B < A - (A - B) / 2 := by linarith [hlt']
      simpa [ε] using hgt'
    linarith
  · have hrestrict :=
      (darbouxIntegral_restrict_to_partitions_with_point (a := a) (b := b) (c := c)
        (f := f) hab hbc hbound').2
    have hmin_ab : ∀ x ∈ Set.Icc a b, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
    have hmax_ab : ∀ x ∈ Set.Icc a b, f x ≤ M := by
      intro x hx
      exact hmax x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
    have hmin_bc : ∀ x ∈ Set.Icc b c, -M ≤ f x := by
      intro x hx
      exact hmin x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
    have hmax_bc : ∀ x ∈ Set.Icc b c, f x ≤ M := by
      intro x hx
      exact hmax x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
    have hBddBelow_ab :
        BddBelow (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) := by
      refine ⟨(-M) * (b - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := a) (b := b) (m := -M) (M := M) hmin_ab hmax_ab P
      exact le_trans hsum.1 hsum.2.1
    have hBddBelow_bc :
        BddBelow (Set.range (fun P : IntervalPartition b c => upperDarbouxSum f P)) := by
      refine ⟨(-M) * (c - b), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := b) (b := c) (m := -M) (M := M) hmin_bc hmax_bc P
      exact le_trans hsum.1 hsum.2.1
    have hT_nonempty :
        (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            upperDarbouxSum f P.1)).Nonempty := by
      rcases intervalPartition_three_points (a := a) (b := b) (c := c) hab hbc with ⟨P0, hbP0⟩
      refine ⟨upperDarbouxSum f P0, ?_⟩
      exact ⟨⟨P0, hbP0⟩, rfl⟩
    have hle :
        upperDarbouxIntegral f a b + upperDarbouxIntegral f b c ≤
          sInf (Set.range (fun P :
            {P : IntervalPartition a c // b ∈ Set.range P.points} =>
              upperDarbouxSum f P.1)) := by
      refine le_csInf hT_nonempty ?_
      intro y hy
      rcases hy with ⟨P, rfl⟩
      rcases intervalPartition_split_at_point (f := f) (P := P.1) P.2 with
        ⟨P1, P2, _, hsum_upper⟩
      have hle1 : upperDarbouxIntegral f a b ≤ upperDarbouxSum f P1 := by
        have hinf := csInf_le hBddBelow_ab (by exact ⟨P1, rfl⟩)
        simpa [upperDarbouxIntegral] using hinf
      have hle2 : upperDarbouxIntegral f b c ≤ upperDarbouxSum f P2 := by
        have hinf := csInf_le hBddBelow_bc (by exact ⟨P2, rfl⟩)
        simpa [upperDarbouxIntegral] using hinf
      calc
        upperDarbouxIntegral f a b + upperDarbouxIntegral f b c
            ≤ upperDarbouxSum f P1 + upperDarbouxSum f P2 := add_le_add hle1 hle2
        _ = upperDarbouxSum f P.1 := hsum_upper.symm
    have hle' : upperDarbouxIntegral f a b + upperDarbouxIntegral f b c ≤
        upperDarbouxIntegral f a c := by
      simpa [hrestrict] using hle
    refine le_antisymm ?_ hle'
    have hnonempty_ab :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) (le_of_lt hab)
      refine ⟨upperDarbouxSum f P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hnonempty_bc :
        (Set.range (fun P : IntervalPartition b c => upperDarbouxSum f P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := b) (b := c) (le_of_lt hbc)
      refine ⟨upperDarbouxSum f P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hBddBelow_S :
        BddBelow (Set.range (fun P :
          {P : IntervalPartition a c // b ∈ Set.range P.points} =>
            upperDarbouxSum f P.1)) := by
      refine ⟨(-M) * (c - a), ?_⟩
      intro y hy
      rcases hy with ⟨P, rfl⟩
      have hsum :=
        lower_upper_sum_bounds (f := f) (a := a) (b := c) (m := -M) (M := M) hmin hmax P.1
      exact le_trans hsum.1 hsum.2.1
    by_contra hlt
    set S := Set.range (fun P :
      {P : IntervalPartition a c // b ∈ Set.range P.points} =>
        upperDarbouxSum f P.1)
    set A : ℝ := upperDarbouxIntegral f a b + upperDarbouxIntegral f b c
    set B : ℝ := sInf S
    have hlt' : A < B := by
      have hlt'' : A < upperDarbouxIntegral f a c := lt_of_not_ge hlt
      simpa [A, B, S, hrestrict] using hlt''
    set ε : ℝ := (B - A) / 2
    have hεpos : 0 < ε := by
      have hεpos' : 0 < (B - A) / 2 := by linarith [hlt']
      simpa [ε] using hεpos'
    have hlt1 :
        sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f P)) <
          upperDarbouxIntegral f a b + ε / 2 := by
      have hlt1' : upperDarbouxIntegral f a b < upperDarbouxIntegral f a b + ε / 2 := by
        linarith [hεpos]
      simpa [upperDarbouxIntegral] using hlt1'
    obtain ⟨y1, ⟨P1, rfl⟩, hP1⟩ := exists_lt_of_csInf_lt hnonempty_ab hlt1
    have hlt2 :
        sInf (Set.range (fun P : IntervalPartition b c => upperDarbouxSum f P)) <
          upperDarbouxIntegral f b c + ε / 2 := by
      have hlt2' : upperDarbouxIntegral f b c < upperDarbouxIntegral f b c + ε / 2 := by
        linarith [hεpos]
      simpa [upperDarbouxIntegral] using hlt2'
    obtain ⟨y2, ⟨P2, rfl⟩, hP2⟩ := exists_lt_of_csInf_lt hnonempty_bc hlt2
    rcases intervalPartition_append (f := f) P1 P2 with ⟨P, hbP, _, hsum_upper⟩
    have hsum_lt : upperDarbouxSum f P < A + ε := by
      have hsum_lt' :
          upperDarbouxSum f P1 + upperDarbouxSum f P2 < A + ε := by
        linarith [hP1, hP2]
      simpa [hsum_upper, add_comm, add_left_comm, add_assoc] using hsum_lt'
    have hmem : upperDarbouxSum f P ∈ S := by
      exact ⟨⟨P, hbP⟩, rfl⟩
    have hle_inf : B ≤ upperDarbouxSum f P := by
      have hle' := csInf_le hBddBelow_S hmem
      simpa [B] using hle'
    have hgt : A + ε < B := by
      have hgt' : A + (B - A) / 2 < B := by linarith [hlt']
      simpa [ε] using hgt'
    linarith

/-- Proposition 5.2.2: For `a < b < c`, a function `f : [a, c] → ℝ` is Riemann
integrable exactly when it is Riemann integrable on both `[a, b]` and `[b, c]`.
If `f` is integrable on `[a, c]`, then the integral splits as
`∫_a^c f = ∫_a^b f + ∫_b^c f`. -/
lemma riemannIntegrableOn_interval_split {a b c : ℝ} {f : ℝ → ℝ}
    (hab : a < b) (hbc : b < c) :
    RiemannIntegrableOn f a c ↔
      RiemannIntegrableOn f a b ∧ RiemannIntegrableOn f b c := by
  classical
  constructor
  · intro hf
    rcases hf with ⟨hbound, hEq⟩
    rcases hbound with ⟨M, hM⟩
    have hbound_ab : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
      refine ⟨M, ?_⟩
      intro x hx
      exact hM x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩
    have hbound_bc : ∃ M : ℝ, ∀ x ∈ Set.Icc b c, |f x| ≤ M := by
      refine ⟨M, ?_⟩
      intro x hx
      exact hM x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩
    have hmin_ab : ∀ x ∈ Set.Icc a b, -M ≤ f x := by
      intro x hx
      exact (abs_le.mp (hM x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩)).1
    have hmax_ab : ∀ x ∈ Set.Icc a b, f x ≤ M := by
      intro x hx
      exact (abs_le.mp (hM x ⟨hx.1, le_trans hx.2 (le_of_lt hbc)⟩)).2
    have hmin_bc : ∀ x ∈ Set.Icc b c, -M ≤ f x := by
      intro x hx
      exact (abs_le.mp (hM x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩)).1
    have hmax_bc : ∀ x ∈ Set.Icc b c, f x ≤ M := by
      intro x hx
      exact (abs_le.mp (hM x ⟨le_trans (le_of_lt hab) hx.1, hx.2⟩)).2
    have hle_ab :
        lowerDarbouxIntegral f a b ≤ upperDarbouxIntegral f a b := by
      have hbounds_ab :=
        lower_upper_integral_bounds (f := f) (a := a) (b := b) (m := -M) (M := M)
          (le_of_lt hab) hmin_ab hmax_ab
      exact hbounds_ab.2.1
    have hle_bc :
        lowerDarbouxIntegral f b c ≤ upperDarbouxIntegral f b c := by
      have hbounds_bc :=
        lower_upper_integral_bounds (f := f) (a := b) (b := c) (m := -M) (M := M)
          (le_of_lt hbc) hmin_bc hmax_bc
      exact hbounds_bc.2.1
    have hsplit :=
      darbouxIntegral_add (a := a) (b := b) (c := c) (f := f) hab hbc ⟨M, hM⟩
    have hsum :
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c =
          upperDarbouxIntegral f a b + upperDarbouxIntegral f b c := by
      calc
        lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c =
            lowerDarbouxIntegral f a c := by
            simpa using hsplit.1.symm
        _ = upperDarbouxIntegral f a c := hEq
        _ = upperDarbouxIntegral f a b + upperDarbouxIntegral f b c := by
            simpa using hsplit.2
    have hEq_ab :
        lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
      linarith [hsum, hle_ab, hle_bc]
    have hEq_bc :
        lowerDarbouxIntegral f b c = upperDarbouxIntegral f b c := by
      linarith [hsum, hle_ab, hle_bc]
    exact ⟨⟨hbound_ab, hEq_ab⟩, ⟨hbound_bc, hEq_bc⟩⟩
  · rintro ⟨hf_ab, hf_bc⟩
    rcases hf_ab with ⟨hbound_ab, hEq_ab⟩
    rcases hf_bc with ⟨hbound_bc, hEq_bc⟩
    rcases hbound_ab with ⟨M1, hM1⟩
    rcases hbound_bc with ⟨M2, hM2⟩
    have hbound_ac : ∃ M : ℝ, ∀ x ∈ Set.Icc a c, |f x| ≤ M := by
      refine ⟨max M1 M2, ?_⟩
      intro x hx
      have hxb : x ≤ b ∨ b ≤ x := le_total x b
      cases hxb with
      | inl hxb =>
          have hxab : x ∈ Set.Icc a b := ⟨hx.1, hxb⟩
          exact le_trans (hM1 x hxab) (le_max_left _ _)
      | inr hbx =>
          have hxbc : x ∈ Set.Icc b c := ⟨hbx, hx.2⟩
          exact le_trans (hM2 x hxbc) (le_max_right _ _)
    have hsplit :=
      darbouxIntegral_add (a := a) (b := b) (c := c) (f := f) hab hbc hbound_ac
    have hEq_ac :
        lowerDarbouxIntegral f a c = upperDarbouxIntegral f a c := by
      calc
        lowerDarbouxIntegral f a c =
            lowerDarbouxIntegral f a b + lowerDarbouxIntegral f b c := hsplit.1
        _ = upperDarbouxIntegral f a b + upperDarbouxIntegral f b c := by
            simp [hEq_ab, hEq_bc]
        _ = upperDarbouxIntegral f a c := by
            simpa using hsplit.2.symm
    exact ⟨hbound_ac, hEq_ac⟩

lemma riemannIntegral_split {a b c : ℝ} {f : ℝ → ℝ} (hab : a < b) (hbc : b < c)
    (hf : RiemannIntegrableOn f a c) :
    ∃ hf_ab : RiemannIntegrableOn f a b,
      ∃ hf_bc : RiemannIntegrableOn f b c,
        riemannIntegral f a c hf =
          riemannIntegral f a b hf_ab + riemannIntegral f b c hf_bc := by
  classical
  obtain ⟨hf_ab, hf_bc⟩ := (riemannIntegrableOn_interval_split hab hbc).1 hf
  refine ⟨hf_ab, hf_bc, ?_⟩
  rcases hf with ⟨hbound, _⟩
  have hsplit :=
    darbouxIntegral_add (a := a) (b := b) (c := c) (f := f) hab hbc hbound
  simpa [riemannIntegral] using hsplit.1

/-- Corollary 5.2.3: If `f ∈ ℛ([a, b])` and `[c, d] ⊆ [a, b]`, then the
restriction of `f` to `[c, d]` belongs to `ℛ([c, d])`. -/
lemma riemannIntegrableOn_subinterval {a b c d : ℝ} {f : ℝ → ℝ}
    (hf : RiemannIntegrableOn f a b) (hac : a ≤ c) (hcd : c ≤ d) (hdb : d ≤ b) :
    RiemannIntegrableOn f c d := by
  classical
  by_cases hcd' : c = d
  · subst d
    have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc c c, |f x| ≤ M := by
      refine ⟨|f c|, ?_⟩
      intro x hx
      have hx' : x = c := le_antisymm hx.2 hx.1
      simp [hx']
    rcases hbound with ⟨M, hM⟩
    have hmin : ∀ x ∈ Set.Icc c c, -M ≤ f x := by
      intro x hx
      have hx' : x = c := le_antisymm hx.2 hx.1
      have hmin_c : -M ≤ f c := (abs_le.mp (hM c ⟨le_rfl, le_rfl⟩)).1
      simpa [hx'] using hmin_c
    have hmax : ∀ x ∈ Set.Icc c c, f x ≤ M := by
      intro x hx
      have hx' : x = c := le_antisymm hx.2 hx.1
      have hmax_c : f c ≤ M := (abs_le.mp (hM c ⟨le_rfl, le_rfl⟩)).2
      simpa [hx'] using hmax_c
    have hbounds :=
      lower_upper_integral_bounds (f := f) (a := c) (b := c) (m := -M) (M := M)
        (by rfl) hmin hmax
    have hEq : lowerDarbouxIntegral f c c = upperDarbouxIntegral f c c := by
      have hlower : 0 ≤ lowerDarbouxIntegral f c c := by
        simpa using hbounds.1
      have hupper : upperDarbouxIntegral f c c ≤ 0 := by
        simpa using hbounds.2.2
      have hle : lowerDarbouxIntegral f c c ≤ upperDarbouxIntegral f c c := hbounds.2.1
      linarith
    exact ⟨⟨M, hM⟩, hEq⟩
  · have hcdlt : c < d := lt_of_le_of_ne hcd hcd'
    by_cases hca : a = c
    · subst hca
      by_cases hdb' : d = b
      · subst hdb'
        simpa using hf
      · have hdb_lt : d < b := lt_of_le_of_ne hdb hdb'
        have had : a < d := by simpa using hcdlt
        have hsplit :=
          (riemannIntegrableOn_interval_split (a := a) (b := d) (c := b) had hdb_lt).1 hf
        simpa using hsplit.1
    · have hca_lt : a < c := lt_of_le_of_ne hac hca
      by_cases hdb' : d = b
      · subst d
        have hcb_lt : c < b := by simpa using hcdlt
        have hsplit :=
          (riemannIntegrableOn_interval_split (a := a) (b := c) (c := b) hca_lt hcb_lt).1 hf
        simpa using hsplit.2
      · have hdb_lt : d < b := lt_of_le_of_ne hdb hdb'
        have had : a < d := lt_trans hca_lt hcdlt
        have hsplit1 :=
          (riemannIntegrableOn_interval_split (a := a) (b := d) (c := b) had hdb_lt).1 hf
        have hf_ad : RiemannIntegrableOn f a d := hsplit1.1
        have hsplit2 :=
          (riemannIntegrableOn_interval_split (a := a) (b := c) (c := d) hca_lt hcdlt).1 hf_ad
        simpa using hsplit2.2

end Section02
end Chap05
