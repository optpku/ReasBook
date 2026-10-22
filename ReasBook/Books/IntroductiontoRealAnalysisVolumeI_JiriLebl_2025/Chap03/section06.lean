/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

open Filter
open BigOperators
open scoped BigOperators

section Chap03
section Section06

/-- Definition 3.6.1: Let `S ⊆ ℝ`. A function `f : ℝ → ℝ` is increasing
(`resp.` strictly increasing) on `S` if `x < y` with `x, y ∈ S` implies
`f x ≤ f y` (`resp.` `f x < f y`). It is decreasing (`resp.` strictly
decreasing) when the inequalities for `f` are reversed. A function that is
either increasing or decreasing on `S` is called monotone on `S`, and if it
is strictly increasing or strictly decreasing on `S`, it is called strictly
monotone on `S`. -/
def increasingOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x < y → f x ≤ f y

def strictlyIncreasingOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x < y → f x < f y

def decreasingOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x < y → f y ≤ f x

def strictlyDecreasingOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  ∀ ⦃x y⦄, x ∈ S → y ∈ S → x < y → f y < f x

def monotoneOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  increasingOn f S ∨ decreasingOn f S

def strictlyMonotoneOn (f : ℝ → ℝ) (S : Set ℝ) : Prop :=
  strictlyIncreasingOn f S ∨ strictlyDecreasingOn f S

lemma increasingOn_iff_monotoneOn_real {f : ℝ → ℝ} {S : Set ℝ} :
    increasingOn f S ↔ MonotoneOn f S := by
  constructor
  · intro h x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · exact h hx hy hlt
    · exact le_rfl
  · intro h x y hx hy hxy
    exact h hx hy (le_of_lt hxy)

lemma strictlyIncreasingOn_iff_strictMonoOn_real {f : ℝ → ℝ} {S : Set ℝ} :
    strictlyIncreasingOn f S ↔ StrictMonoOn f S := by
  constructor
  · intro h x hx y hy hxy
    exact h hx hy hxy
  · intro h x y hx hy hxy
    exact h hx hy hxy

lemma decreasingOn_iff_antitoneOn_real {f : ℝ → ℝ} {S : Set ℝ} :
    decreasingOn f S ↔ AntitoneOn f S := by
  constructor
  · intro h x hx y hy hxy
    rcases lt_or_eq_of_le hxy with hlt | rfl
    · exact h hx hy hlt
    · exact le_rfl
  · intro h x y hx hy hxy
    exact h hx hy (le_of_lt hxy)

lemma strictlyDecreasingOn_iff_strictAntiOn_real {f : ℝ → ℝ} {S : Set ℝ} :
    strictlyDecreasingOn f S ↔ StrictAntiOn f S := by
  constructor
  · intro h x hx y hy hxy
    exact h hx hy hxy
  · intro h x y hx hy hxy
    exact h hx hy hxy

lemma monotoneOn_iff_monotoneOrAntitone {f : ℝ → ℝ} {S : Set ℝ} :
    monotoneOn f S ↔ MonotoneOn f S ∨ AntitoneOn f S := by
  constructor
  · intro h
    rcases h with h | h
    · left
      exact (increasingOn_iff_monotoneOn_real).1 h
    · right
      exact (decreasingOn_iff_antitoneOn_real).1 h
  · intro h
    rcases h with h | h
    · left
      exact (increasingOn_iff_monotoneOn_real).2 h
    · right
      exact (decreasingOn_iff_antitoneOn_real).2 h

lemma strictlyMonotoneOn_iff_strictMonoOrStrictAnti {f : ℝ → ℝ} {S : Set ℝ} :
    strictlyMonotoneOn f S ↔ StrictMonoOn f S ∨ StrictAntiOn f S := by
  constructor
  · intro h
    rcases h with h | h
    · left
      exact (strictlyIncreasingOn_iff_strictMonoOn_real).1 h
    · right
      exact (strictlyDecreasingOn_iff_strictAntiOn_real).1 h
  · intro h
    rcases h with h | h
    · left
      exact (strictlyIncreasingOn_iff_strictMonoOn_real).2 h
    · right
      exact (strictlyDecreasingOn_iff_strictAntiOn_real).2 h

/-- A technical lemma: if `f` is monotone on `S`, then the left limit along
`S ∩ (-∞, c)` converges to the supremum of the left slice when that slice is
bounded above. -/
lemma monotoneOn_left_limit_sup {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f S) (hc : c ∈ closure (S ∩ Set.Iio c))
    (hB : BddAbove (f '' (S ∩ Set.Iio c))) :
    Tendsto f (nhdsWithin c (S ∩ Set.Iio c))
      (nhds (sSup (f '' (S ∩ Set.Iio c)))) := by
  classical
  have hne : (S ∩ Set.Iio c).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S ∩ Set.Iio c) with h | h
    · have : False := by
        simp [h] at hc
      exact this.elim
    · exact h
  refine tendsto_order.2 ?_
  constructor
  · intro b hb
    have h_exists : ∃ x ∈ S ∩ Set.Iio c, b < f x := by
      classical
      by_contra h
      have hcontra : ∀ x, x ∈ S ∩ Set.Iio c → f x ≤ b := by
        classical
        have h' := h
        push_neg at h'
        intro x hx
        exact h' x hx
      have hSup_le : sSup (f '' (S ∩ Set.Iio c)) ≤ b := by
        refine csSup_le (hne.image _) ?_
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hcontra x hx
      exact (not_lt_of_ge hSup_le hb).elim
    rcases h_exists with ⟨x0, hx0, hbfx0⟩
    have hx0lt : x0 < c := hx0.2
    have hδpos : 0 < (c - x0) / 2 := by linarith
    have hsubset :
        Metric.ball c ((c - x0) / 2) ∩ (S ∩ Set.Iio c) ⊆ {x | b < f x} := by
      intro x hx
      have hxball : dist x c < (c - x0) / 2 := by
        simpa [Metric.ball] using hx.1
      have hdist : |x - c| < (c - x0) / 2 := by
        simpa [Real.dist_eq, abs_sub_comm] using hxball
      have hcx : c - x < (c - x0) / 2 := by
        linarith [(abs_lt.mp hdist).1]
      have hxgt : x0 < x := by linarith
      have hmono : f x0 ≤ f x := hf hx0.1 hx.2.1 (le_of_lt hxgt)
      exact lt_of_lt_of_le hbfx0 hmono
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Metric.ball c ((c - x0) / 2), Metric.ball_mem_nhds _ hδpos,
            S ∩ Set.Iio c, by simp, ?_⟩
    intro x hx
    exact hsubset hx
  · intro b hb
    have hsubset : S ∩ Set.Iio c ⊆ {x | f x < b} := by
      intro x hx
      have hxle : f x ≤ sSup (f '' (S ∩ Set.Iio c)) :=
        le_csSup hB ⟨x, hx, rfl⟩
      exact lt_of_le_of_lt hxle hb
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Set.univ, Filter.univ_mem, S ∩ Set.Iio c, by simp, ?_⟩
    intro x hx
    exact hsubset hx.2

lemma monotoneOn_left_limit_atTop {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f S) (hc : c ∈ closure (S ∩ Set.Iio c))
    (hUnb : ¬ BddAbove (f '' (S ∩ Set.Iio c))) :
    Tendsto f (nhdsWithin c (S ∩ Set.Iio c)) atTop := by
  classical
  have hne : (S ∩ Set.Iio c).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S ∩ Set.Iio c) with h | h
    · have : False := by
        simp [h] at hc
      exact this.elim
    · exact h
  refine tendsto_atTop.2 ?_
  intro M
  rcases not_bddAbove_iff.1 hUnb M with ⟨y, hy, hMy⟩
  rcases hy with ⟨x0, hx0, rfl⟩
  have hx0lt : x0 < c := hx0.2
  have hδpos : 0 < (c - x0) / 2 := by linarith
  have hsubset :
      Metric.ball c ((c - x0) / 2) ∩ (S ∩ Set.Iio c) ⊆ {x | M ≤ f x} := by
    intro x hx
    have hxball : dist x c < (c - x0) / 2 := by
      simpa [Metric.ball] using hx.1
    have hdist : |x - c| < (c - x0) / 2 := by
      simpa [Real.dist_eq, abs_sub_comm] using hxball
    have hcx : c - x < (c - x0) / 2 := by
      linarith [(abs_lt.mp hdist).1]
    have hxgt : x0 < x := by linarith
    have hmono : f x0 ≤ f x := hf hx0.1 hx.2.1 (le_of_lt hxgt)
    exact le_trans (le_of_lt hMy) hmono
  refine mem_inf_iff_superset.2 ?_
  refine ⟨Metric.ball c ((c - x0) / 2), Metric.ball_mem_nhds _ hδpos,
          S ∩ Set.Iio c, by simp, ?_⟩
  intro x hx
  exact hsubset hx

lemma monotoneOn_right_limit_inf {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f S) (hc : c ∈ closure (S ∩ Set.Ioi c))
    (hB : BddBelow (f '' (S ∩ Set.Ioi c))) :
    Tendsto f (nhdsWithin c (S ∩ Set.Ioi c))
      (nhds (sInf (f '' (S ∩ Set.Ioi c)))) := by
  classical
  have hne : (S ∩ Set.Ioi c).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S ∩ Set.Ioi c) with h | h
    · have : False := by
        simp [h] at hc
      exact this.elim
    · exact h
  refine tendsto_order.2 ?_
  constructor
  · intro b hb
    have hsubset : S ∩ Set.Ioi c ⊆ {x | b < f x} := by
      intro x hx
      have hle : sInf (f '' (S ∩ Set.Ioi c)) ≤ f x :=
        csInf_le hB ⟨x, hx, rfl⟩
      exact lt_of_lt_of_le hb hle
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Set.univ, Filter.univ_mem, S ∩ Set.Ioi c, by simp, ?_⟩
    intro x hx
    exact hsubset hx.2
  · intro b hb
    have h_exists : ∃ x ∈ S ∩ Set.Ioi c, f x < b := by
      classical
      by_contra h
      have hcontra : ∀ x, x ∈ S ∩ Set.Ioi c → b ≤ f x := by
        classical
        have h' := h
        push_neg at h'
        intro x hx
        exact h' x hx
      have hInf_ge : b ≤ sInf (f '' (S ∩ Set.Ioi c)) := by
        refine le_csInf (hne.image _) ?_
        intro y hy
        rcases hy with ⟨x, hx, rfl⟩
        exact hcontra x hx
      exact (not_lt_of_ge hInf_ge hb).elim
    rcases h_exists with ⟨x0, hx0, hfx0lt⟩
    have hx0gt : c < x0 := hx0.2
    have hδpos : 0 < (x0 - c) / 2 := by linarith
    have hsubset :
        Metric.ball c ((x0 - c) / 2) ∩ (S ∩ Set.Ioi c) ⊆ {x | f x < b} := by
      intro x hx
      have hxball : dist x c < (x0 - c) / 2 := by
        simpa [Metric.ball] using hx.1
      have hdist : |x - c| < (x0 - c) / 2 := by
        simpa [Real.dist_eq] using hxball
      have hxlt : x - c < (x0 - c) / 2 := (abs_lt.mp hdist).2
      have hxc : x < x0 := by linarith
      have hmono : f x ≤ f x0 := hf hx.2.1 hx0.1 (le_of_lt hxc)
      exact lt_of_le_of_lt hmono hfx0lt
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Metric.ball c ((x0 - c) / 2), Metric.ball_mem_nhds _ hδpos,
            S ∩ Set.Ioi c, by simp, ?_⟩
    intro x hx
    exact hsubset hx

lemma monotoneOn_right_limit_atBot {S : Set ℝ} {f : ℝ → ℝ} {c : ℝ}
    (hf : MonotoneOn f S) (hc : c ∈ closure (S ∩ Set.Ioi c))
    (hUnb : ¬ BddBelow (f '' (S ∩ Set.Ioi c))) :
    Tendsto f (nhdsWithin c (S ∩ Set.Ioi c)) atBot := by
  classical
  have hne : (S ∩ Set.Ioi c).Nonempty := by
    rcases Set.eq_empty_or_nonempty (S ∩ Set.Ioi c) with h | h
    · have : False := by
        simp [h] at hc
      exact this.elim
    · exact h
  refine tendsto_atBot.2 ?_
  intro M
  rcases not_bddBelow_iff.1 hUnb M with ⟨y, hy, hyM⟩
  rcases hy with ⟨x0, hx0, rfl⟩
  have hx0gt : c < x0 := hx0.2
  have hδpos : 0 < (x0 - c) / 2 := by linarith
  have hsubset :
      Metric.ball c ((x0 - c) / 2) ∩ (S ∩ Set.Ioi c) ⊆ {x | f x ≤ M} := by
    intro x hx
    have hxball : dist x c < (x0 - c) / 2 := by
      simpa [Metric.ball] using hx.1
    have hdist : |x - c| < (x0 - c) / 2 := by
      simpa [Real.dist_eq] using hxball
    have hxlt : x - c < (x0 - c) / 2 := (abs_lt.mp hdist).2
    have hxc : x < x0 := by linarith
    have hmono : f x ≤ f x0 := hf hx.2.1 hx0.1 (le_of_lt hxc)
    exact le_trans hmono (le_of_lt hyM)
  refine mem_inf_iff_superset.2 ?_
  refine ⟨Metric.ball c ((x0 - c) / 2), Metric.ball_mem_nhds _ hδpos,
          S ∩ Set.Ioi c, by simp, ?_⟩
  intro x hx
  exact hsubset hx

lemma monotoneOn_limit_atTop_cases {S : Set ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f S)
    (hS : Filter.NeBot ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)) :
    (BddAbove (f '' S) →
        Tendsto f ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
          (nhds (sSup (f '' S)))) ∧
    (¬ BddAbove (f '' S) →
        Tendsto f ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) atTop) := by
  classical
  have hneS : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with h | h
    · have : ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) = ⊥ := by
        simp [h]
      exact (hS.ne this).elim
    · exact h
  constructor
  · intro hB
    refine tendsto_order.2 ?_
    constructor
    · intro b hb
      have h_exists : ∃ x ∈ S, b < f x := by
        classical
        by_contra h
        have hcontra : ∀ x, x ∈ S → f x ≤ b := by
          classical
          have h' := h
          push_neg at h'
          intro x hx
          exact h' x hx
        have hSup_le : sSup (f '' S) ≤ b := by
          refine csSup_le ?_ ?_
          · exact hneS.image _
          · intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            exact hcontra x hx
        exact (not_lt_of_ge hSup_le hb).elim
      rcases h_exists with ⟨x0, hx0, hfx0⟩
      have hsubset :
          Set.Ici x0 ∩ S ⊆ {x | b < f x} := by
        intro x hx
        have hmono : f x0 ≤ f x := hf hx0 hx.2 hx.1
        exact lt_of_lt_of_le hfx0 hmono
      refine mem_inf_iff_superset.2 ?_
      refine ⟨Set.Ici x0, ?_, S, by simp, ?_⟩
      · exact (mem_atTop_sets).2 ⟨x0, by intro x hx; exact hx⟩
      · intro x hx
        exact hsubset hx
    · intro b hb
      have hsubset : S ⊆ {x | f x < b} := by
        intro x hx
        have hxle : f x ≤ sSup (f '' S) := le_csSup hB ⟨x, hx, rfl⟩
        exact lt_of_le_of_lt hxle hb
      refine mem_inf_iff_superset.2 ?_
      refine ⟨Set.univ, Filter.univ_mem, S, by simp, ?_⟩
      intro x hx
      exact hsubset hx.2
  · intro hUnb
    refine tendsto_atTop.2 ?_
    intro M
    rcases not_bddAbove_iff.1 hUnb M with ⟨y, hy, hyM⟩
    rcases hy with ⟨x0, hx0, rfl⟩
    have hsubset : Set.Ici x0 ∩ S ⊆ {x | M ≤ f x} := by
      intro x hx
      have hmono : f x0 ≤ f x := hf hx0 hx.2 hx.1
      exact le_trans (le_of_lt hyM) hmono
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Set.Ici x0, ?_, S, by simp, ?_⟩
    · exact (mem_atTop_sets).2 ⟨x0, by intro x hx; exact hx⟩
    · intro x hx
      exact hsubset hx

lemma monotoneOn_limit_atBot_cases {S : Set ℝ} {f : ℝ → ℝ}
    (hf : MonotoneOn f S)
    (hS : Filter.NeBot ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)) :
    (BddBelow (f '' S) →
        Tendsto f ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
          (nhds (sInf (f '' S)))) ∧
    (¬ BddBelow (f '' S) →
        Tendsto f ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) atBot) := by
  classical
  have hneS : S.Nonempty := by
    rcases Set.eq_empty_or_nonempty S with h | h
    · have : ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) = ⊥ := by
        simp [h]
      exact (hS.ne this).elim
    · exact h
  constructor
  · intro hB
    refine tendsto_order.2 ?_
    constructor
    · intro b hb
      have hsubset : S ⊆ {x | b < f x} := by
        intro x hx
        have hle : sInf (f '' S) ≤ f x := csInf_le hB ⟨x, hx, rfl⟩
        exact lt_of_lt_of_le hb hle
      refine mem_inf_iff_superset.2 ?_
      refine ⟨Set.univ, Filter.univ_mem, S, by simp, ?_⟩
      intro x hx
      exact hsubset hx.2
    · intro b hb
      have h_exists : ∃ x ∈ S, f x < b := by
        classical
        by_contra h
        have hcontra : ∀ x, x ∈ S → b ≤ f x := by
          classical
          have h' := h
          push_neg at h'
          intro x hx
          exact h' x hx
        have hInf_ge : b ≤ sInf (f '' S) := by
          refine le_csInf (hneS.image _) ?_
          intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact hcontra x hx
        exact (not_lt_of_ge hInf_ge hb).elim
      rcases h_exists with ⟨x0, hx0, hfx0lt⟩
      have hsubset :
          Set.Iic x0 ∩ S ⊆ {x | f x < b} := by
        intro x hx
        have hmono : f x ≤ f x0 := hf hx.2 hx0 hx.1
        exact lt_of_le_of_lt hmono hfx0lt
      refine mem_inf_iff_superset.2 ?_
      refine ⟨Set.Iic x0, ?_, S, by simp, ?_⟩
      · exact (mem_atBot_sets).2 ⟨x0, by intro x hx; exact hx⟩
      · intro x hx
        exact hsubset hx
  · intro hUnb
    refine tendsto_atBot.2 ?_
    intro M
    rcases not_bddBelow_iff.1 hUnb M with ⟨y, hy, hyM⟩
    rcases hy with ⟨x0, hx0, rfl⟩
    have hsubset : Set.Iic x0 ∩ S ⊆ {x | f x ≤ M} := by
      intro x hx
      have hmono : f x ≤ f x0 := hf hx.2 hx0 hx.1
      exact le_trans hmono (le_of_lt hyM)
    refine mem_inf_iff_superset.2 ?_
    refine ⟨Set.Iic x0, ?_, S, by simp, ?_⟩
    · exact (mem_atBot_sets).2 ⟨x0, by intro x hx; exact hx⟩
    · intro x hx
      exact hsubset hx

lemma antitoneOn_left_limit_inf {S : Set ℝ} {g : ℝ → ℝ} {c : ℝ}
    (hg : AntitoneOn g S) (hc : c ∈ closure (S ∩ Set.Iio c))
    (hB : BddBelow (g '' (S ∩ Set.Iio c))) :
    Tendsto g (nhdsWithin c (S ∩ Set.Iio c))
      (nhds (sInf (g '' (S ∩ Set.Iio c)))) := by
  have hmono : MonotoneOn (-g) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  rcases hB with ⟨m, hm⟩
  have hB' : BddAbove ((-g) '' (S ∩ Set.Iio c)) := by
    refine ⟨-m, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have : m ≤ g x := hm ⟨x, hx, rfl⟩
    simpa using (neg_le_neg this)
  have hlim := monotoneOn_left_limit_sup hmono hc hB'
  have hneg_fun :
      Tendsto (fun x => g x) (nhdsWithin c (S ∩ Set.Iio c))
        (nhds (- sSup ((-g) '' (S ∩ Set.Iio c)))) := by
    simpa [Function.comp, Pi.neg_apply, neg_neg] using (hlim.neg)
  have hneg :
      Tendsto g (nhdsWithin c (S ∩ Set.Iio c))
        (nhds (- sSup ((-g) '' (S ∩ Set.Iio c)))) := by
    simpa using hneg_fun
  have himage :
      - (g '' (S ∩ Set.Iio c)) = (-g) '' (S ∩ Set.Iio c) := by
    simpa [Function.comp] using
      (Set.image_image (fun x => -x) g (S ∩ Set.Iio c))
  have hneg_set :
      Tendsto g (nhdsWithin c (S ∩ Set.Iio c))
        (nhds (- sSup (- (g '' (S ∩ Set.Iio c))))) := by
    simpa [himage] using hneg
  simpa only [Real.sInf_def] using hneg_set

lemma antitoneOn_left_limit_atBot {S : Set ℝ} {g : ℝ → ℝ} {c : ℝ}
    (hg : AntitoneOn g S) (hc : c ∈ closure (S ∩ Set.Iio c))
    (hUnb : ¬ BddBelow (g '' (S ∩ Set.Iio c))) :
    Tendsto g (nhdsWithin c (S ∩ Set.Iio c)) atBot := by
  have hmono : MonotoneOn (-g) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  have hUnb' : ¬ BddAbove ((-g) '' (S ∩ Set.Iio c)) := by
    intro h
    rcases h with ⟨M, hM⟩
    apply hUnb
    refine ⟨-M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hxM : (-g x) ≤ M := hM ⟨x, hx, rfl⟩
    have : -M ≤ g x := by linarith
    exact this
  have hlim := monotoneOn_left_limit_atTop hmono hc hUnb'
  exact (tendsto_neg_atTop_iff).1 hlim

lemma antitoneOn_right_limit_sup {S : Set ℝ} {g : ℝ → ℝ} {c : ℝ}
    (hg : AntitoneOn g S) (hc : c ∈ closure (S ∩ Set.Ioi c))
    (hB : BddAbove (g '' (S ∩ Set.Ioi c))) :
    Tendsto g (nhdsWithin c (S ∩ Set.Ioi c))
      (nhds (sSup (g '' (S ∩ Set.Ioi c)))) := by
  have hmono : MonotoneOn (-g) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  rcases hB with ⟨M, hM⟩
  have hB' : BddBelow ((-g) '' (S ∩ Set.Ioi c)) := by
    refine ⟨-M, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    have hxM : g x ≤ M := hM ⟨x, hx, rfl⟩
    exact neg_le_neg hxM
  have hlim := monotoneOn_right_limit_inf hmono hc hB'
  have hneg_fun :
      Tendsto (fun x => g x) (nhdsWithin c (S ∩ Set.Ioi c))
        (nhds (- sInf ((-g) '' (S ∩ Set.Ioi c)))) := by
    simpa [Function.comp, Pi.neg_apply, neg_neg] using (hlim.neg)
  have hneg :
      Tendsto g (nhdsWithin c (S ∩ Set.Ioi c))
        (nhds (- sInf ((-g) '' (S ∩ Set.Ioi c)))) := by
    simpa using hneg_fun
  have himage :
      - (g '' (S ∩ Set.Ioi c)) = (-g) '' (S ∩ Set.Ioi c) := by
    simpa [Function.comp] using
      (Set.image_image (fun x => -x) g (S ∩ Set.Ioi c))
  have hneg_set :
      Tendsto g (nhdsWithin c (S ∩ Set.Ioi c))
        (nhds (- sInf (- (g '' (S ∩ Set.Ioi c))))) := by
    simpa [himage] using hneg
  simpa [Real.sInf_def] using hneg_set

lemma antitoneOn_right_limit_atTop {S : Set ℝ} {g : ℝ → ℝ} {c : ℝ}
    (hg : AntitoneOn g S) (hc : c ∈ closure (S ∩ Set.Ioi c))
    (hUnb : ¬ BddAbove (g '' (S ∩ Set.Ioi c))) :
    Tendsto g (nhdsWithin c (S ∩ Set.Ioi c)) atTop := by
  have hmono : MonotoneOn (fun x => -g x) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  have hUnb' : ¬ BddBelow ((fun x => -g x) '' (S ∩ Set.Ioi c)) := by
    intro h
    rcases h with ⟨M, hM⟩
    apply hUnb
    refine ⟨-M, ?_⟩
    intro y hy
    rcases hy with ⟨x, hx, rfl⟩
    have hbound : M ≤ -g x := hM ⟨x, hx, rfl⟩
    have : g x ≤ -M := by linarith
    exact this
  have hlim := monotoneOn_right_limit_atBot hmono hc hUnb'
  exact (tendsto_neg_atBot_iff).1 hlim

lemma antitoneOn_limit_atTop_cases {S : Set ℝ} {g : ℝ → ℝ}
    (hg : AntitoneOn g S)
    (hS : Filter.NeBot ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)) :
    (BddBelow (g '' S) →
        Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
          (nhds (sInf (g '' S)))) ∧
    (¬ BddBelow (g '' S) →
        Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) atBot) := by
  have hmono : MonotoneOn (fun x => -g x) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  have hcases := monotoneOn_limit_atTop_cases hmono hS
  constructor
  · intro hB
    rcases hB with ⟨m, hm⟩
    have hB' : BddAbove ((-g) '' S) := by
      refine ⟨-m, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hx : m ≤ g x := hm ⟨x, hx, rfl⟩
      have : (-g x) ≤ -m := by linarith
      exact this
    have hlim := hcases.1 hB'
    have hneg_fun :
        Tendsto (fun x => g x) ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sSup ((-g) '' S))) := by
      simpa [Function.comp, Pi.neg_apply, neg_neg] using (hlim.neg)
    have hneg :
        Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sSup ((-g) '' S))) := by
      simpa using hneg_fun
    have himage : - (g '' S) = (-g) '' S := by
      simpa [Function.comp] using (Set.image_image (fun x => -x) g S)
    have hneg_set :
        Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sSup (- (g '' S)))) := by
      simpa [himage] using hneg
    simpa only [Real.sInf_def] using hneg_set
  · intro hUnb
    have hUnb' : ¬ BddAbove ((-g) '' S) := by
      intro h
      rcases h with ⟨M, hM⟩
      apply hUnb
      refine ⟨-M, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxM : (-g x) ≤ M := hM ⟨x, hx, rfl⟩
      have : -M ≤ g x := by linarith
      exact this
    have hlim := hcases.2 hUnb'
    exact (tendsto_neg_atTop_iff).1 hlim

lemma antitoneOn_limit_atBot_cases {S : Set ℝ} {g : ℝ → ℝ}
    (hg : AntitoneOn g S)
    (hS : Filter.NeBot ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)) :
    (BddAbove (g '' S) →
        Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
          (nhds (sSup (g '' S)))) ∧
    (¬ BddAbove (g '' S) →
        Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) atTop) := by
  have hmono : MonotoneOn (-g) S := by
    intro x hx y hy hxy
    exact neg_le_neg (hg hx hy hxy)
  have hcases := monotoneOn_limit_atBot_cases hmono hS
  constructor
  · intro hB
    rcases hB with ⟨m, hm⟩
    have hB' : BddBelow ((-g) '' S) := by
      refine ⟨-m, ?_⟩
      rintro y ⟨x, hx, rfl⟩
      have hx : g x ≤ m := hm ⟨x, hx, rfl⟩
      have : -m ≤ -g x := by linarith
      exact this
    have hlim := hcases.1 hB'
    have hneg_fun :
        Tendsto (fun x => g x) ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sInf ((-g) '' S))) := by
      simpa [Function.comp, Pi.neg_apply, neg_neg] using (hlim.neg)
    have hneg :
        Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sInf ((-g) '' S))) := by
      simpa using hneg_fun
    have himage : - (g '' S) = (-g) '' S := by
      simpa [Function.comp] using (Set.image_image (fun x => -x) g S)
    have hneg_set :
        Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
          (nhds (- sInf (- (g '' S)))) := by
      simpa [himage] using hneg
    simpa [Real.sInf_def] using hneg_set
  · intro hUnb
    have hUnb' : ¬ BddBelow ((-g) '' S) := by
      intro h
      rcases h with ⟨M, hM⟩
      apply hUnb
      refine ⟨-M, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hxM : M ≤ -g x := hM ⟨x, hx, rfl⟩
      have : g x ≤ -M := by linarith
      exact this
    have hlim := hcases.2 hUnb'
    exact (tendsto_neg_atBot_iff).1 hlim

/-- Proposition 3.6.2: Let `S ⊆ ℝ`, `c ∈ ℝ`, `f : ℝ → ℝ` be increasing on `S`,
and `g : ℝ → ℝ` be decreasing on `S`. If `c` is a cluster point of
`S ∩ (-∞, c)`, then `lim_{x → c^-} f x = sup {f x | x ∈ S, x < c}` and
`lim_{x → c^-} g x = inf {g x | x ∈ S, x < c}`. If `c` is a cluster point of
`S ∩ (c, ∞)`, then `lim_{x → c^+} f x = inf {f x | x ∈ S, x > c}` and
`lim_{x → c^+} g x = sup {g x | x ∈ S, x > c}`. If `∞` is a cluster point of
`S`, then `lim_{x → ∞} f x = sup {f x | x ∈ S}` and
`lim_{x → ∞} g x = inf {g x | x ∈ S}`. If `-∞` is a cluster point of `S`, then
`lim_{x → -∞} f x = inf {f x | x ∈ S}` and
`lim_{x → -∞} g x = sup {g x | x ∈ S}`. -/
lemma proposition_3_6_2 {S : Set ℝ} {c : ℝ} {f g : ℝ → ℝ}
    (hf : MonotoneOn f S) (hg : AntitoneOn g S) :
    (c ∈ closure (S ∩ Set.Iio c) →
        (BddAbove (f '' (S ∩ Set.Iio c)) →
            Tendsto f (nhdsWithin c (S ∩ Set.Iio c))
              (nhds (sSup (f '' (S ∩ Set.Iio c))))) ∧
        (¬ BddAbove (f '' (S ∩ Set.Iio c)) →
            Tendsto f (nhdsWithin c (S ∩ Set.Iio c)) atTop) ∧
        (BddBelow (g '' (S ∩ Set.Iio c)) →
            Tendsto g (nhdsWithin c (S ∩ Set.Iio c))
              (nhds (sInf (g '' (S ∩ Set.Iio c))))) ∧
        (¬ BddBelow (g '' (S ∩ Set.Iio c)) →
            Tendsto g (nhdsWithin c (S ∩ Set.Iio c)) atBot)) ∧
    (c ∈ closure (S ∩ Set.Ioi c) →
        (BddBelow (f '' (S ∩ Set.Ioi c)) →
            Tendsto f (nhdsWithin c (S ∩ Set.Ioi c))
              (nhds (sInf (f '' (S ∩ Set.Ioi c))))) ∧
        (¬ BddBelow (f '' (S ∩ Set.Ioi c)) →
            Tendsto f (nhdsWithin c (S ∩ Set.Ioi c)) atBot) ∧
        (BddAbove (g '' (S ∩ Set.Ioi c)) →
            Tendsto g (nhdsWithin c (S ∩ Set.Ioi c))
              (nhds (sSup (g '' (S ∩ Set.Ioi c))))) ∧
        (¬ BddAbove (g '' (S ∩ Set.Ioi c)) →
            Tendsto g (nhdsWithin c (S ∩ Set.Ioi c)) atTop)) ∧
    (Filter.NeBot ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) →
        (BddAbove (f '' S) →
            Tendsto f ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
              (nhds (sSup (f '' S)))) ∧
        (¬ BddAbove (f '' S) →
            Tendsto f ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) atTop) ∧
        (BddBelow (g '' S) →
            Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S)
              (nhds (sInf (g '' S)))) ∧
        (¬ BddBelow (g '' S) →
            Tendsto g ((Filter.atTop : Filter ℝ) ⊓ Filter.principal S) atBot)) ∧
    (Filter.NeBot ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) →
        (BddBelow (f '' S) →
            Tendsto f ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
              (nhds (sInf (f '' S)))) ∧
        (¬ BddBelow (f '' S) →
            Tendsto f ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) atBot) ∧
        (BddAbove (g '' S) →
            Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S)
              (nhds (sSup (g '' S)))) ∧
        (¬ BddAbove (g '' S) →
            Tendsto g ((Filter.atBot : Filter ℝ) ⊓ Filter.principal S) atTop)) := by
  constructor
  · intro hc
    constructor
    · intro hB
      exact monotoneOn_left_limit_sup hf hc hB
    · constructor
      · intro hUnb
        exact monotoneOn_left_limit_atTop hf hc hUnb
      · constructor
        · intro hBg
          exact antitoneOn_left_limit_inf hg hc hBg
        · intro hUnb
          exact antitoneOn_left_limit_atBot hg hc hUnb
  · constructor
    · intro hc
      constructor
      · intro hB
        exact monotoneOn_right_limit_inf hf hc hB
      · constructor
        · intro hUnb
          exact monotoneOn_right_limit_atBot hf hc hUnb
        · constructor
          · intro hBg
            exact antitoneOn_right_limit_sup hg hc hBg
          · intro hUnb
            exact antitoneOn_right_limit_atTop hg hc hUnb
    · constructor
      · intro hS
        have hcases := monotoneOn_limit_atTop_cases hf hS
        have hcases_g := antitoneOn_limit_atTop_cases hg hS
        constructor
        · intro hB
          exact hcases.1 hB
        · constructor
          · intro hUnb
            exact hcases.2 hUnb
          · constructor
            · intro hBg
              exact hcases_g.1 hBg
            · intro hUnb
              exact hcases_g.2 hUnb
      · intro hS
        have hcases := monotoneOn_limit_atBot_cases hf hS
        have hcases_g := antitoneOn_limit_atBot_cases hg hS
        constructor
        · intro hB
          exact hcases.1 hB
        · constructor
          · intro hUnb
            exact hcases.2 hUnb
          · constructor
            · intro hBg
              exact hcases_g.1 hBg
            · intro hUnb
              exact hcases_g.2 hUnb

/-- If an interval `I` contains a point strictly to the left of `c`, then `c`
is a closure point of `I ∩ (-∞, c)`. -/
lemma closure_left_slice_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected)
    {c : I} (hleft : ∃ x ∈ I, x < c) :
    (c : ℝ) ∈ closure (I ∩ Set.Iio (c : ℝ)) := by
  rcases hleft with ⟨x0, hx0I, hx0c⟩
  have hsubset : Set.Ioo x0 (c : ℝ) ⊆ I ∩ Set.Iio (c : ℝ) := by
    intro x hx
    have hxI : x ∈ I := by
      have hseg := hI.out hx0I c.property
      exact hseg ⟨hx.1.le, hx.2.le⟩
    exact ⟨hxI, hx.2⟩
  have hc_mem : (c : ℝ) ∈ closure (Set.Ioo x0 (c : ℝ)) := by
    have hclosure : closure (Set.Ioo (x0 : ℝ) c) = Set.Icc (x0 : ℝ) c := by
      simpa using closure_Ioo (ne_of_lt hx0c)
    have hcIcc : (c : ℝ) ∈ Set.Icc (x0 : ℝ) c := by
      simp [hx0c.le]
    simpa [hclosure] using hcIcc
  exact closure_mono hsubset hc_mem

/-- If an interval `I` contains a point strictly to the right of `c`, then `c`
is a closure point of `I ∩ (c, ∞)`. -/
lemma closure_right_slice_of_ordConnected {I : Set ℝ} (hI : I.OrdConnected)
    {c : I} (hright : ∃ x ∈ I, c < x) :
    (c : ℝ) ∈ closure (I ∩ Set.Ioi (c : ℝ)) := by
  rcases hright with ⟨x0, hx0I, hcx0⟩
  have hsubset : Set.Ioo (c : ℝ) x0 ⊆ I ∩ Set.Ioi (c : ℝ) := by
    intro x hx
    have hxI : x ∈ I := by
      have hseg := hI.out c.property hx0I
      exact hseg ⟨hx.1.le, hx.2.le⟩
    exact ⟨hxI, hx.1⟩
  have hc_mem : (c : ℝ) ∈ closure (Set.Ioo (c : ℝ) x0) := by
    have hclosure : closure (Set.Ioo (c : ℝ) x0) = Set.Icc (c : ℝ) x0 := by
      simpa using closure_Ioo (ne_of_lt hcx0)
    have hcIcc : (c : ℝ) ∈ Set.Icc (c : ℝ) x0 := by
      simp [hcx0.le]
    simpa [hclosure] using hcIcc
  exact closure_mono hsubset hc_mem

/-- Corollary 3.6.3: If `I ⊆ ℝ` is an interval and `f : I → ℝ` is monotone and
not constant, then the image `f(I)` is an interval if and only if `f` is
continuous. -/
theorem monotone_range_interval_iff_continuous {I : Set ℝ} (hI : I.OrdConnected)
    {f : I → ℝ} (hf : Monotone f) (hconst : ∃ x y : I, f x ≠ f y) :
    Set.OrdConnected (Set.range f) ↔ Continuous f := by
  classical
  constructor
  · intro hOC
    -- Argue by contrapositive: a discontinuity produces a gap in the range.
    by_contra hcont
    have hnotall : ¬ ∀ x : I, ContinuousAt f x := by
      intro h
      exact hcont (continuous_iff_continuousAt.mpr h)
    rcases not_forall.mp hnotall with ⟨c, hnc⟩
    -- Extend `f` to a monotone function on `ℝ` so that we can work with the
    -- one-sided limits provided by proposition 3.6.2.
    let g : ℝ → ℝ := fun x => if hx : x ∈ I then f ⟨x, hx⟩ else f c
    have hg_mono : MonotoneOn g I := by
      intro x hx y hy hxy
      have hxy' : (⟨x, hx⟩ : I) ≤ ⟨y, hy⟩ := hxy
      have hmono := hf hxy'
      simpa [g, hx, hy] using hmono
    -- `I` contains a point different from `c`.
    have hneI : ∃ z : I, z ≠ c := by
      rcases hconst with ⟨x0, x1, hval⟩
      by_cases hxc : x0 = c
      · refine ⟨x1, ?_⟩
        intro h
        apply hval
        calc
          f x0 = f c := by simp [hxc]
          _ = f x1 := by simp [h]
      · exact ⟨x0, hxc⟩
    rcases hneI with ⟨z, hzne⟩
    have hside : (∃ x ∈ I, x < c) ∨ (∃ x ∈ I, c < x) := by
      have hzlt_or : z < c ∨ c < z := lt_or_gt_of_ne hzne
      cases hzlt_or with
      | inl hlt => exact Or.inl ⟨z, z.property, hlt⟩
      | inr hgt => exact Or.inr ⟨z, z.property, hgt⟩
    classical
    have hantic : AntitoneOn (fun x => -g x) I := by
      intro x hx y hy hxy
      exact neg_le_neg (hg_mono hx hy hxy)
    have hrange : Set.range f = g '' I := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, by simp [g, x.property]⟩
      · rintro ⟨x, hxI, rfl⟩
        exact ⟨⟨x, hxI⟩, by simp [g, hxI]⟩
    -- Non-continuity transfers to the extension `g` within `I`.
    have hnot_cont_within : ¬ ContinuousWithinAt g I (c : ℝ) := by
      intro hcont_within
      apply hnc
      have hcomp :
          ContinuousWithinAt (fun x : I => g x) Set.univ c :=
        hcont_within.comp
          (continuous_subtype_val.continuousWithinAt :
            ContinuousWithinAt Subtype.val Set.univ c)
          (by intro x hx; simp [x.property])
      have hcont_restrict : ContinuousAt (fun x : I => g x) c := by
        simpa [ContinuousWithinAt, nhdsWithin_univ] using hcomp
      have hfg : (fun x : I => g x) = f := by
        funext x; simp [g, x.property]
      simpa [hfg] using hcont_restrict
    have hnot_left_or_right :
        ¬ ContinuousWithinAt g (I ∩ Set.Iio (c : ℝ)) (c : ℝ) ∨
          ¬ ContinuousWithinAt g (I ∩ Set.Ioi (c : ℝ)) (c : ℝ) := by
      have hiff :=
        (continuousWithinAt_iff_continuous_left'_right' (a := (c : ℝ))
            (f := g) (s := I))
      have hnot := mt hiff.mpr hnot_cont_within
      classical
      by_contra h
      push_neg at h
      exact hnot ⟨h.1, h.2⟩
    -- Useful bounds.
    let a := sSup (g '' (I ∩ Set.Iio (c : ℝ)))
    let b := sInf (g '' (I ∩ Set.Ioi (c : ℝ)))
    have hleft_bdd : BddAbove (g '' (I ∩ Set.Iio (c : ℝ))) := by
      refine ⟨g c, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hg_mono hx.1 c.property (le_of_lt hx.2)
    have hright_bdd : BddBelow (g '' (I ∩ Set.Ioi (c : ℝ))) := by
      refine ⟨g c, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      exact hg_mono c.property hx.1 (le_of_lt hx.2)
    have hleft_bound : ∀ {x}, x ∈ I → x < c → g x ≤ a := by
      intro x hxI hxlt
      have hxset : x ∈ I ∩ Set.Iio (c : ℝ) := ⟨hxI, hxlt⟩
      exact le_csSup hleft_bdd ⟨x, hxset, rfl⟩
    have hright_bound : ∀ {x}, x ∈ I → c < x → b ≤ g x := by
      intro x hxI hxgt
      have hxset : x ∈ I ∩ Set.Ioi (c : ℝ) := ⟨hxI, hxgt⟩
      exact csInf_le hright_bdd ⟨x, hxset, rfl⟩
    have hprop :=
      proposition_3_6_2 (S := I) (c := (c : ℝ)) (f := g)
        (g := fun x => -g x) hg_mono hantic
    -- Split depending on the side of discontinuity.
    rcases hnot_left_or_right with hleft_fail | hright_fail
    · -- Discontinuity from the left.
      -- There must be a point strictly to the left of `c`.
      have hleft_exists : ∃ x ∈ I, x < c := by
        classical
        by_contra hnone
        have hset : I ∩ Set.Iio (c : ℝ) = ∅ := by
          ext x; constructor
          · intro hx; rcases hx with ⟨hxI, hxlt⟩; exact (hnone ⟨x, hxI, hxlt⟩).elim
          · intro hx; cases hx
        have hcont_left : ContinuousWithinAt g (I ∩ Set.Iio (c : ℝ)) (c : ℝ) := by
          simp [ContinuousWithinAt, hset, tendsto_bot]
        exact hleft_fail hcont_left
      rcases hleft_exists with ⟨x1, hx1I, hx1lt⟩
      have hclosure := closure_left_slice_of_ordConnected hI ⟨x1, hx1I, hx1lt⟩
      have hleft_limit :
          Tendsto g (nhdsWithin (c : ℝ) (I ∩ Set.Iio (c : ℝ))) (nhds a) :=
        (hprop.1 hclosure).1 hleft_bdd
      have ha_le_gc : a ≤ g c := by
        refine csSup_le ?_ ?_
        · exact ⟨g x1, ⟨x1, ⟨hx1I, hx1lt⟩, rfl⟩⟩
        · intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact hg_mono hx.1 c.property (le_of_lt hx.2)
      have hneq : a ≠ g c := by
        intro h
        apply hleft_fail
        simpa [h, a] using hleft_limit
      have ha_lt_gc : a < g c := lt_of_le_of_ne ha_le_gc hneq
      obtain ⟨y, hay, hyc⟩ := exists_between ha_lt_gc
      have hy_not : y ∉ Set.range f := by
        intro hy
        rcases hy with ⟨w, rfl⟩
        rcases lt_trichotomy (w : ℝ) (c : ℝ) with hxc | hxc | hxc
        · have hxI : (w : ℝ) ∈ I := w.property
          have hxy : g w ≤ a := hleft_bound hxI hxc
          have hgx : g w = (f w) := by simp [g, w.property]
          have hay' : a < g w := by simpa [hgx] using hay
          linarith
        · have hxc' : (w : ℝ) = c := hxc
          have hx_sub : w = c := Subtype.ext hxc'
          have hyc' : (f c : ℝ) < f c := by
            have hyc₁ : f w < g c := by simpa using hyc
            have hyc₂ : f c < g c := by simpa [hx_sub] using hyc₁
            have hgc : g c = f c := by simp [g, c.property]
            exact hgc ▸ hyc₂
          exact (lt_irrefl _ : ¬ (f c : ℝ) < f c) hyc'
        · have hxI : (w : ℝ) ∈ I := w.property
          have hmono : g c ≤ g w := hg_mono c.property hxI (le_of_lt hxc)
          have hgx : g w = (f w) := by simp [g, w.property]
          have hyc' : g w < g c := by
            have hyc' : f w < g c := by simpa using hyc
            simpa [hgx] using hyc'
          exact (not_lt_of_ge hmono) hyc'
      have hx1range : g x1 ∈ g '' I := ⟨x1, hx1I, rfl⟩
      have hcrange : g c ∈ g '' I := ⟨c, c.property, rfl⟩
      have hyIcc : y ∈ Set.Icc (g x1) (g c) := by
        refine ⟨?_, ?_⟩
        · have hx1le : g x1 ≤ a := hleft_bound hx1I hx1lt
          linarith
        · linarith
      have hy_range : y ∈ Set.range f :=
        hOC.out (by simpa [hrange] using hx1range) (by simpa [hrange] using hcrange)
          hyIcc
      exact hy_not hy_range
    · -- Discontinuity from the right.
      have hright_exists : ∃ x ∈ I, c < x := by
        classical
        by_contra hnone
        have hset : I ∩ Set.Ioi (c : ℝ) = ∅ := by
          ext x; constructor
          · intro hx; rcases hx with ⟨hxI, hxgt⟩; exact (hnone ⟨x, hxI, hxgt⟩).elim
          · intro hx; cases hx
        have hcont_right : ContinuousWithinAt g (I ∩ Set.Ioi (c : ℝ)) (c : ℝ) := by
          simp [ContinuousWithinAt, hset, tendsto_bot]
        exact hright_fail hcont_right
      rcases hright_exists with ⟨x2, hx2I, hcx2⟩
      have hclosure := closure_right_slice_of_ordConnected hI ⟨x2, hx2I, hcx2⟩
      have hright_limit :
          Tendsto g (nhdsWithin (c : ℝ) (I ∩ Set.Ioi (c : ℝ))) (nhds b) :=
        (hprop.2.1 hclosure).1 hright_bdd
      have hgc_le_b : g c ≤ b := by
        refine le_csInf ?_ ?_
        · exact ⟨g x2, ⟨x2, ⟨hx2I, hcx2⟩, rfl⟩⟩
        · intro y hy
          rcases hy with ⟨x, hx, rfl⟩
          exact hg_mono c.property hx.1 (le_of_lt hx.2)
      have hneq : b ≠ g c := by
        intro h
        apply hright_fail
        simpa [h, b] using hright_limit
      have gc_lt_b : g c < b := lt_of_le_of_ne hgc_le_b hneq.symm
      obtain ⟨y, hyc, hyb⟩ := exists_between gc_lt_b
      have hy_not : y ∉ Set.range f := by
        intro hy
        rcases hy with ⟨w, rfl⟩
        rcases lt_trichotomy (w : ℝ) (c : ℝ) with hxc | hxc | hxc
        · have hxI : (w : ℝ) ∈ I := w.property
          have hmono : g w ≤ g c := hg_mono hxI c.property (le_of_lt hxc)
          have hgx : g w = (f w) := by simp [g, hxI]
          have hyc' : g c < g w := by
            have hyc'' : g c < f w := by simpa using hyc
            simpa [hgx] using hyc''
          exact (not_lt_of_ge hmono) hyc'
        · have hxc' : (w : ℝ) = c := hxc
          have hx_sub : w = c := Subtype.ext hxc'
          have hyc' : (f c : ℝ) < f c := by
            have hyc₁ : g c < f w := by simpa using hyc
            have hyc₂ : g c < f c := by simpa [hx_sub] using hyc₁
            have hgc : g c = f c := by simp [g, c.property]
            exact hgc ▸ hyc₂
          exact (lt_irrefl _ : ¬ (f c : ℝ) < f c) hyc'
        · have hxI : (w : ℝ) ∈ I := w.property
          have hxgt : c < w := hxc
          have hxbound : b ≤ g w := hright_bound hxI hxgt
          have hgx : g w = (f w) := by simp [g, hxI]
          have hyb' : g w < b := by
            have hyb'' : f w < b := by simpa using hyb
            simpa [hgx] using hyb''
          exact (not_lt_of_ge hxbound) hyb'
      have hcrange : g c ∈ g '' I := ⟨c, c.property, rfl⟩
      have hx2range : g x2 ∈ g '' I := ⟨x2, hx2I, rfl⟩
      have hyIcc : y ∈ Set.Icc (g c) (g x2) := by
        refine ⟨?_, ?_⟩
        · linarith
        · have hxb : b ≤ g x2 := hright_bound hx2I hcx2
          linarith
      have hy_range : y ∈ Set.range f :=
        hOC.out (by simpa [hrange] using hcrange) (by simpa [hrange] using hx2range)
          hyIcc
      exact hy_not hy_range
  · intro hcont
    refine Set.OrdConnected.mk ?_
    intro a ha b hb y hy
    rcases ha with ⟨x1, rfl⟩
    rcases hb with ⟨x2, rfl⟩
    rcases le_total x1 x2 with hle | hle
    · have hsubset : Set.Icc (x1 : ℝ) (x2 : ℝ) ⊆ I :=
        hI.out x1.property x2.property
      classical
      let g : ℝ → ℝ := fun t => if ht : t ∈ I then f ⟨t, ht⟩ else f x1
      have hcont_incl :
          Continuous fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) =>
            (⟨(t : ℝ), hsubset t.property⟩ : I) :=
        (continuous_subtype_val :
            Continuous fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) => (t : ℝ)).subtype_mk
          (by intro t; exact hsubset t.property)
      have hcont_sub : Continuous fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) => g t := by
        have hfun_eq :
            (fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) => g t) =
              (fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) =>
                f ⟨(t : ℝ), hsubset t.property⟩) := by
          funext t
          have htI : (t : ℝ) ∈ I := hsubset t.property
          simp [g, htI]
        have hcomp :
            Continuous fun t : Set.Icc (x1 : ℝ) (x2 : ℝ) =>
              f ⟨(t : ℝ), hsubset t.property⟩ :=
          hcont.comp hcont_incl
        simpa [hfun_eq] using hcomp
      have hcont_on : ContinuousOn g (Set.Icc (x1 : ℝ) (x2 : ℝ)) :=
        (continuousOn_iff_continuous_restrict).2 hcont_sub
      have hIVT := intermediate_value_Icc (a := (x1 : ℝ)) (b := (x2 : ℝ))
        hle hcont_on
      have hy' : y ∈ Set.Icc (g (x1 : ℝ)) (g (x2 : ℝ)) := by
        simpa [g, x1.property, x2.property] using hy
      have hgy : y ∈ g '' Set.Icc (x1 : ℝ) (x2 : ℝ) := hIVT hy'
      rcases hgy with ⟨t, htmem, hgt⟩
      have htI : t ∈ I := hsubset htmem
      refine ⟨⟨t, htI⟩, ?_⟩
      have : g t = f ⟨t, htI⟩ := by simp [g, htI]
      simpa [this] using hgt
    · have hfx : f x2 ≤ f x1 := hf hle
      have hy_le : y ≤ f x1 := le_trans hy.2 hfx
      have hy_eq : y = f x1 := le_antisymm hy_le hy.1
      refine ⟨x1, by simp [hy_eq]⟩

/-- Corollary 3.6.4: Let `I ⊆ ℝ` be an interval and `f : I → ℝ` be monotone. Then
`f` has at most countably many discontinuities. -/
theorem monotone_discontinuities_countable {I : Set ℝ} (hI : I.OrdConnected)
    {f : I → ℝ} (hf : Monotone f) :
    Set.Countable {x : I | ¬ ContinuousAt f x} := by
  simpa using (hf.countable_not_continuousAt : Set.Countable
    {x : I | ¬ ContinuousAt f x})
/-- Example 3.6.5: There exists a strictly increasing function `f : [0, 1] → ℝ`
that is bounded and has a discontinuity at each point `1 - 1/k` for
`k ∈ ℕ`. In particular, it is monotone on a compact interval with
countably many discontinuities. -/
lemma example_3_6_5 :
    ∃ f : ℝ → ℝ,
      StrictMonoOn f (Set.Icc 0 1) ∧
      BddBelow (f '' Set.Icc 0 1) ∧ BddAbove (f '' Set.Icc 0 1) ∧
      (∀ k : ℕ, ¬ ContinuousAt f (1 - (1 / (k.succ : ℝ)))) ∧
      Set.Countable {x : ℝ | x ∈ Set.Icc 0 1 ∧ ¬ ContinuousAt f x} := by
  classical
  -- Jump locations and helper partial sums.
  let c : ℕ → ℝ := fun k => 1 - (1 / (k.succ : ℝ))
  let g : ℝ → ℝ :=
    fun x =>
      Finset.sum (Finset.range (Nat.floor (1 / (1 - x)) + 1))
        (fun n => (1 / 2 : ℝ) ^ n)
  let f : ℝ → ℝ := fun x => if hx : x < 1 then x + g x else 3
  have hg_nonneg : ∀ x, 0 ≤ g x := by
    intro x
    refine Finset.sum_nonneg ?_
    intro n hn
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    exact this
  have hg_mono_lt1 :
      ∀ {x y : ℝ}, x < 1 → y < 1 → x ≤ y → g x ≤ g y := by
    intro x y hx1 hy1 hxy
    have hposx : 0 < 1 - x := by linarith
    have hposy : 0 < 1 - y := by linarith
    have hdiv_le : 1 / (1 - x) ≤ 1 / (1 - y) :=
      one_div_le_one_div_of_le hposy (by linarith)
    have hfloor_le :
        Nat.floor (1 / (1 - x)) ≤ Nat.floor (1 / (1 - y)) :=
      Nat.floor_mono hdiv_le
    have hsubset :
        Finset.range (Nat.floor (1 / (1 - x)) + 1) ⊆
          Finset.range (Nat.floor (1 / (1 - y)) + 1) := by
      intro n hn
      exact Finset.mem_range.2
        (lt_of_lt_of_le (Finset.mem_range.1 hn) (Nat.succ_le_succ hfloor_le))
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro n hn hn'
    have : 0 ≤ (1 / 2 : ℝ) ^ n := by positivity
    exact this
  have hgeom : Summable (fun n : ℕ => (1 / 2 : ℝ) ^ n) :=
    (summable_geometric_iff_norm_lt_one).2 (by norm_num)
  have hgeom_tsum : tsum (fun n : ℕ => (1 / 2 : ℝ) ^ n) = (2 : ℝ) := by
    have hsum :
        tsum (fun n : ℕ => (1 / 2 : ℝ) ^ n) =
          (1 - (1 / 2 : ℝ))⁻¹ :=
      tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)
    calc
      tsum (fun n : ℕ => (1 / 2 : ℝ) ^ n) =
          (1 - (1 / 2 : ℝ))⁻¹ := hsum
      _ = (2 : ℝ) := by norm_num
  have hgeom_tsum_inv : tsum (fun n : ℕ => (2 : ℝ)⁻¹ ^ n) = (2 : ℝ) := by
    simpa [one_div] using hgeom_tsum
  have hgeom_tsum_pow : tsum (fun n : ℕ => (2 ^ n : ℝ)⁻¹) = (2 : ℝ) := by
    simpa [one_div, inv_pow] using hgeom_tsum_inv
  have hg_le_two : ∀ x, g x ≤ 2 := by
    intro x
    have hnonneg : ∀ n : ℕ, 0 ≤ (1 / 2 : ℝ) ^ n := by
      intro n; positivity
    have hbound :=
      Summable.sum_le_tsum
        (s := Finset.range (Nat.floor (1 / (1 - x)) + 1))
        (f := fun n : ℕ => (1 / 2 : ℝ) ^ n)
        (by intro n hn; exact hnonneg n) hgeom
    have hbound' : Finset.sum (Finset.range (Nat.floor (1 / (1 - x)) + 1))
        (fun n : ℕ => (1 / 2 : ℝ) ^ n) ≤ (2 : ℝ) := by
      simpa [one_div, inv_pow, hgeom_tsum_pow] using hbound
    simpa [g] using hbound'
  have hstrict : StrictMonoOn f (Set.Icc 0 1) := by
    intro x hx y hy hxy
    have hxlt1 : x < 1 := lt_of_lt_of_le hxy hy.2
    by_cases hy1 : y < 1
    · have hylt1 : y < 1 := hy1
      have hgle : g x ≤ g y := hg_mono_lt1 hxlt1 hylt1 hxy.le
      have hxval : f x = x + g x := by simp [f, hxlt1]
      have hyval : f y = y + g y := by simp [f, hylt1]
      linarith
    · have hy1' : y = 1 := by linarith [hy.2, hy1]
      subst hy1'
      have hxval : f x = x + g x := by simp [f, hxlt1]
      have hyval : f (1 : ℝ) = 3 := by simp [f]
      have hgle : g x ≤ 2 := hg_le_two x
      have hx_lt3 : f x < 3 := by linarith
      linarith
  have hbddBelow : BddBelow (f '' Set.Icc 0 1) := by
    refine ⟨0, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    by_cases hxlt1 : x < 1
    · have hxval : f x = x + g x := by simp [f, hxlt1]
      have hx0 : 0 ≤ x := hx.1
      have hg0 : 0 ≤ g x := hg_nonneg x
      linarith
    · have hx1 : x = 1 := by linarith [hx.2, hxlt1]
      subst hx1
      simp [f]
  have hbddAbove : BddAbove (f '' Set.Icc 0 1) := by
    refine ⟨3, ?_⟩
    rintro y ⟨x, hx, rfl⟩
    by_cases hxlt1 : x < 1
    · have hxval : f x = x + g x := by simp [f, hxlt1]
      have hgle : g x ≤ 2 := hg_le_two x
      linarith [hxval, hx.2, hgle]
    · have hx1 : x = 1 := by linarith [hx.2, hxlt1]
      subst hx1
      simp [f]
  have h_discont : ∀ k : ℕ, ¬ ContinuousAt f (c k) := by
    intro k
    set ck : ℝ := c k
    have hck_lt1 : ck < 1 := by
      have hkpos : 0 < (k.succ : ℝ) := by exact_mod_cast Nat.succ_pos k
      have hpos : 0 < 1 / (k.succ : ℝ) := by
        have := inv_pos.mpr hkpos
        simpa using this
      linarith [hpos]
    have hfloor_ck : Nat.floor (1 / (1 - ck)) = k.succ := by
      have hden : 1 - ck = 1 / (k.succ : ℝ) := by
        simp [c, ck]
      have hval : 1 / (1 - ck) = (k.succ : ℝ) := by
        simp [hden]
      calc
        Nat.floor (1 / (1 - ck))
            = Nat.floor ((k + 1 : ℝ)) := by
              simp [hval, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
        _ = k + 1 := by
          simpa using (Nat.floor_natCast (k + 1))
    have hcont_hfun :
        ContinuousAt (fun x : ℝ => 1 / (1 - x)) ck := by
      have hneq : (1 - ck) ≠ 0 := by
        have hpos : 0 < 1 - ck := by linarith
        exact ne_of_gt hpos
      have hcont := (continuousAt_const.sub continuousAt_id).inv₀ hneq
      simpa [one_div, ck, c] using hcont
    have hpowpos : 0 < (1 / 2 : ℝ) ^ k.succ := by positivity
    set ε : ℝ := (1 / 2 : ℝ) ^ k.succ / 2
    have hεpos : 0 < ε := by
      change 0 < (1 / 2 : ℝ) ^ k.succ / 2
      exact half_pos hpowpos
    intro hfcont
    rcases (Metric.continuousAt_iff.1 hfcont) ε hεpos with ⟨δ, hδpos, hδ⟩
    rcases (Metric.continuousAt_iff.1 hcont_hfun) (1 / 2) (by norm_num) with
      ⟨δ0, hδ0pos, hδ0⟩
    let δ' := min δ δ0
    have hδ'pos : 0 < δ' := lt_min hδpos hδ0pos
    let x : ℝ := ck - δ' / 2
    have hxlt_ck : x < ck := by
      have hpos : (0 : ℝ) < δ' / 2 := by linarith
      dsimp [x] at hpos ⊢
      linarith
    have hxlt1 : x < 1 := by linarith [hck_lt1, hxlt_ck]
    have hdist_x_ck : dist x ck = δ' / 2 := by
      have hxck : x - ck = -(δ' / 2) := by dsimp [x]; ring
      have hneg : x - ck < 0 := by linarith [hxck, hδ'pos]
      have hdist : dist x ck = |x - ck| := by simp [Real.dist_eq]
      have habs : |x - ck| = δ' / 2 := by
        have habs_neg : |x - ck| = -(x - ck) := abs_of_neg hneg
        have hxpos : -(x - ck) = δ' / 2 := by linarith [hxck]
        linarith
      linarith
    have hdist_lt_δ : dist x ck < δ := by
      have hδ'_le : δ' ≤ δ := min_le_left _ _
      linarith [hdist_x_ck, hδ'_le, hδpos]
    have hdist_lt_δ0 : dist x ck < δ0 := by
      have hδ'_le : δ' ≤ δ0 := min_le_right _ _
      linarith [hdist_x_ck, hδ'_le, hδ0pos]
    have hckinv : (1 - ck)⁻¹ = (k.succ : ℝ) := by
      have hden : 1 - ck = 1 / (k.succ : ℝ) := by simp [c, ck]
      simp [hden]
    have hclose :
        |1 / (1 - x) - (k.succ : ℝ)| < 1 / 2 := by
      have := hδ0 hdist_lt_δ0
      simpa [Real.dist_eq, hckinv] using this
    have hlt_succ : 1 / (1 - x) < (k.succ : ℝ) := by
      have hden_gt : 1 - ck < 1 - x := by linarith
      have hpos_ck : 0 < 1 - ck := by linarith
      have hckval : 1 / (1 - ck) = (k.succ : ℝ) := by
        have hden : 1 - ck = 1 / (k.succ : ℝ) := by simp [c, ck]
        simp [hden]
      have hxval : 1 / (1 - x) < 1 / (1 - ck) :=
        one_div_lt_one_div_of_lt hpos_ck hden_gt
      simpa [hckval] using hxval
    have hgt : (k : ℝ) < 1 / (1 - x) := by
      have hbounds := abs_lt.mp hclose
      have hneg : -(1 / 2) < 1 / (1 - x) - (k.succ : ℝ) := hbounds.1
      have hlow : (k.succ : ℝ) - 1 / 2 < 1 / (1 - x) := by linarith [hneg]
      have hklt : (k : ℝ) < (k.succ : ℝ) - 1 / 2 := by
        have hpos : (0 : ℝ) < (1 / 2 : ℝ) := by norm_num
        have hsucc : (k.succ : ℝ) = k + 1 := by norm_cast
        linarith
      exact lt_trans hklt hlow
    have hxpos : 0 ≤ 1 / (1 - x) := by
      have hpos : 0 < 1 - x := by linarith
      have hpos' : 0 < 1 / (1 - x) := by
        have hpos'' : 0 < (1 - x)⁻¹ := inv_pos.mpr hpos
        simpa [one_div] using hpos''
      exact hpos'.le
    have hfloor_x : Nat.floor (1 / (1 - x)) = k := by
      refine (Nat.floor_eq_iff hxpos).mpr ?_
      constructor
      · exact le_of_lt hgt
      · have hlt_succ' : 1 / (1 - x) < (k : ℝ) + 1 := by
          simpa [Nat.succ_eq_add_one] using hlt_succ
        exact hlt_succ'
    have hfloor_x_inv : Nat.floor ((1 - x)⁻¹) = k := by
      simpa [one_div] using hfloor_x
    have hxval : f x = x + g x := by simp [f, hxlt1]
    have hckval : f ck = ck + g ck := by simp [f, hck_lt1]
    have hgx :
        g x = Finset.sum (Finset.range k.succ) (fun n => (1 / 2 : ℝ) ^ n) := by
      dsimp [g]
      simp [hfloor_x_inv]
    have hgc :
        g ck =
          Finset.sum (Finset.range (k.succ + 1)) (fun n => (1 / 2 : ℝ) ^ n) := by
      dsimp [g]
      have hfloor_ck_inv : Nat.floor ((1 - ck)⁻¹) = k.succ := by
        simpa [one_div] using hfloor_ck
      simp [hfloor_ck_inv]
    have hsum :
        g ck - g x = (1 / 2 : ℝ) ^ k.succ := by
      have hsum' :=
        Finset.sum_range_succ (f := fun n => (1 / 2 : ℝ) ^ n) k.succ
      have hckg :
          g ck =
            Finset.sum (Finset.range k.succ) (fun n => (1 / 2 : ℝ) ^ n) +
              (1 / 2 : ℝ) ^ k.succ := by
        simpa [hgc] using hsum'
      have hxg :
          g x = Finset.sum (Finset.range k.succ) (fun n => (1 / 2 : ℝ) ^ n) := by
        simp [hgx]
      calc
        g ck - g x
            = (Finset.sum (Finset.range k.succ) (fun n => (1 / 2 : ℝ) ^ n) +
                (1 / 2 : ℝ) ^ k.succ) -
              Finset.sum (Finset.range k.succ) (fun n => (1 / 2 : ℝ) ^ n) := by
              linarith [hckg, hxg]
        _ = (1 / 2 : ℝ) ^ k.succ := by ring
    have hfx_lt : f x < f ck := by
      have hgle : g x ≤ g ck := by
        have hxle : x ≤ ck := by linarith
        exact hg_mono_lt1 hxlt1 hck_lt1 hxle
      linarith [hxval, hckval, hxlt_ck, hgle]
    have hdist_fx_ck : dist (f x) (f ck) = f ck - f x := by
      have hneg : f x - f ck < 0 := by linarith
      simp [Real.dist_eq, abs_of_neg hneg]
    have hdiff :
        f ck - f x = (ck - x) + (1 / 2 : ℝ) ^ k.succ := by
      linarith [hxval, hckval, hsum]
    have hdist_lower :
        (1 / 2 : ℝ) ^ k.succ ≤ dist (f x) (f ck) := by
      have hge : (1 / 2 : ℝ) ^ k.succ ≤ f ck - f x := by linarith
      linarith [hdist_fx_ck, hge]
    have hlt_eps : dist (f x) (f ck) < ε := by
      have hdist' : dist x ck < δ := hdist_lt_δ
      exact hδ hdist'
    have hε_le : ε ≤ (1 / 2 : ℝ) ^ k.succ := by
      change (1 / 2 : ℝ) ^ k.succ / 2 ≤ (1 / 2 : ℝ) ^ k.succ
      exact div_le_self (by positivity : 0 ≤ (1 / 2 : ℝ) ^ k.succ) (by norm_num : (1 : ℝ) ≤ 2)
    have hnot : ¬ dist (f x) (f ck) < ε := by
      have hge := le_trans hε_le hdist_lower
      linarith
    exact (hnot hlt_eps).elim
  have hfmono : Monotone f := by
    intro x y hxy
    by_cases hx1 : x < 1
    · by_cases hy1 : y < 1
      · have hgle : g x ≤ g y := hg_mono_lt1 hx1 hy1 hxy
        have hxval : f x = x + g x := by simp [f, hx1]
        have hyval : f y = y + g y := by simp [f, hy1]
        linarith
      · have hyge : (1 : ℝ) ≤ y := by linarith
        have hbound : f x ≤ 3 := by
          have hgle : g x ≤ 2 := hg_le_two x
          have hxval : f x = x + g x := by simp [f, hx1]
          have hxle : x ≤ 1 := le_of_lt hx1
          linarith [hxval, hgle, hxle]
        have : f y = 3 := by simp [f, hy1]
        linarith
    · have hxge : (1 : ℝ) ≤ x := le_of_not_gt hx1
      have hyge : (1 : ℝ) ≤ y := le_trans hxge hxy
      simp [f, hx1, (not_lt_of_ge hyge)]  -- both branches give `3`
  have hcountable :
      Set.Countable {x : ℝ | x ∈ Set.Icc 0 1 ∧ ¬ ContinuousAt f x} := by
    have hsubset :
        {x : ℝ | x ∈ Set.Icc 0 1 ∧ ¬ ContinuousAt f x} ⊆
          {x : ℝ | ¬ ContinuousAt f x} := by
      intro x hx
      exact hx.2
    have hcount := hfmono.countable_not_continuousAt
    exact hcount.mono hsubset
  refine ⟨f, hstrict, hbddBelow, hbddAbove, ?_, ?_⟩
  · intro k
    simpa [c] using h_discont k
  · exact hcountable

/-- Proposition 3.6.6: If `I ⊆ ℝ` is an interval and `f : I → ℝ` is strictly
monotone, then the inverse `f⁻¹ : f(I) → I` is continuous. -/
theorem proposition_3_6_6 {I : Set ℝ} (hI : I.OrdConnected) {f : I → ℝ}
    (hf : StrictMono f) (hTop : OrderTopology ↥(Set.range f)) :
    Continuous ((StrictMono.orderIso f hf).symm) := by
  classical
  let _ : OrderTopology ↥(Set.range f) := hTop
  have hcont := (StrictMono.orderIso f hf).toHomeomorph.symm.continuous
  have hcont' : Continuous ((StrictMono.orderIso f hf).symm) := by
    simpa using hcont
  simpa using hcont'

/-- Example 3.6.7: The piecewise function `f : ℝ → ℝ` given by
`f x = x` for `x < 0` and `f x = x + 1` for `x ≥ 0` is not continuous at `0`,
its image of `ℝ` is `(-∞, 0) ∪ [1, ∞)`, and the inverse function
`f⁻¹ : (-∞, 0) ∪ [1, ∞) → ℝ` defined by `y` if `y < 0` and `y - 1` if `y ≥ 1`
is continuous. -/
lemma example_3_6_7 :
    (let f : ℝ → ℝ := fun x => if x < 0 then x else x + 1
     let S : Set ℝ := {y : ℝ | y < 0 ∨ 1 ≤ y}
     let g : S → ℝ := fun y => if (y : ℝ) < 0 then (y : ℝ) else (y : ℝ) - 1
     ¬ ContinuousAt f 0 ∧ Set.image f Set.univ = S ∧ Continuous g) := by
  classical
  dsimp
  constructor
  · -- `f` is not continuous at `0` (jump from `0` to `1`)
    intro hf
    have h0 : (fun x : ℝ => if x < 0 then x else x + 1) 0 = 1 := by simp
    rcases (Metric.continuousAt_iff.1 hf) (1 / 2) (by norm_num) with ⟨δ, hδpos, hδ⟩
    let x : ℝ := -(δ / 2)
    have hxlt : x < 0 := by
      have hδpos' : 0 < δ / 2 := by linarith
      simpa [x] using hδpos'
    have hx_dist : dist x 0 < δ := by
      have hx : dist x 0 = δ / 2 := by
        have hδnonneg : 0 ≤ δ / 2 := by linarith
        calc
          dist x 0 = |x| := by simp
          _ = |δ / 2| := by simp [x]
          _ = δ / 2 := by simp [abs_of_nonneg hδnonneg]
      linarith
    have hfx : (fun x : ℝ => if x < 0 then x else x + 1) x = x := by
      simp [x, hxlt]
    have hdist_ge : (1 / 2 : ℝ) < dist x 1 := by
      have hxpos : (1 / 2 : ℝ) < 1 - x := by linarith
      have hxabs : |x - 1| = 1 - x := by
        have hx1 : x - 1 ≤ 0 := by linarith
        have hxabs' : |x - 1| = -(x - 1) := abs_of_nonpos hx1
        have hneg : -(x - 1) = 1 - x := by ring
        simpa [hneg] using hxabs'
      have hdist : dist x 1 = 1 - x := by
        simp [Real.dist_eq, hxabs]
      simpa [hdist] using hxpos
    have hcontra : dist x 1 < 1 / 2 := by
      have h := hδ hx_dist
      simpa [hfx] using h
    linarith
  · constructor
    · -- image of `f` is `(-∞, 0) ∪ [1, ∞)`
      ext y
      constructor
      · intro hy
        rcases hy with ⟨x, -, rfl⟩
        by_cases hx : x < 0
        · simp [hx]
        · have hx0 : 0 ≤ x := le_of_not_gt hx
          have h1 : 1 ≤ x + 1 := by linarith
          simp [hx, h1]
      · intro hy
        rcases hy with hyneg | hypos
        · refine ⟨y, by trivial, ?_⟩
          simp [hyneg]
        · refine ⟨y - 1, by trivial, ?_⟩
          have hx : ¬ y - 1 < 0 := by
            have hx0 : 0 ≤ y - 1 := by linarith
            exact not_lt.mpr hx0
          simp [hx, sub_add_cancel]
    · -- continuity of the explicit inverse `g`
      let h : ℝ → ℝ := fun x : ℝ => if x < 0 then x else x - 1
      have h_cont_neg : ∀ {y : ℝ}, y < 0 → ContinuousAt h y := by
        intro y hy
        have hIio : Set.Iio (0 : ℝ) ∈ nhds y :=
          IsOpen.mem_nhds isOpen_Iio hy
        have heq : h =ᶠ[nhds y] fun x => x := by
          refine Filter.eventually_of_mem hIio ?_
          intro x hx
          have hxlt : x < 0 := hx
          simp [h, hxlt]
        have hlim : Tendsto h (nhds y) (nhds y) :=
          (tendsto_congr' heq).2 tendsto_id
        have hyval : h y = y := by simp [h, hy]
        simpa [ContinuousAt, hyval] using hlim
      have h_cont_pos : ∀ {y : ℝ}, 0 < y → ContinuousAt h y := by
        intro y hy
        have hIoi : Set.Ioi (0 : ℝ) ∈ nhds y :=
          IsOpen.mem_nhds isOpen_Ioi hy
        have heq : h =ᶠ[nhds y] fun x => x - 1 := by
          refine Filter.eventually_of_mem hIoi ?_
          intro x hx
          have hx0 : ¬ x < 0 := not_lt.mpr (le_of_lt hx)
          simp [h, hx0]
        have hlin : ContinuousAt (fun x : ℝ => x - 1) y := by
          simpa [sub_eq_add_neg] using
            (continuousAt_id.add (continuousAt_const : ContinuousAt (fun _ : ℝ => (-1 : ℝ)) y))
        have hlim : Tendsto h (nhds y) (nhds (y - 1)) :=
          (tendsto_congr' heq).2 hlin.tendsto
        have hyval : h y = y - 1 := by
          have hy0 : ¬ y < 0 := not_lt.mpr (le_of_lt hy)
          simp [h, hy0]
        simpa [ContinuousAt, hyval] using hlim
      have hcont : Continuous fun y : {y : ℝ | y < 0 ∨ 1 ≤ y} => h y := by
        refine continuous_iff_continuousAt.mpr ?_
        intro y
        rcases y.property with hyneg | hyge
        · have hycont : ContinuousAt h (y : ℝ) := h_cont_neg hyneg
          simpa [h] using hycont.comp continuous_subtype_val.continuousAt
        · have hypos : 0 < (y : ℝ) := by linarith
          have hycont : ContinuousAt h (y : ℝ) := h_cont_pos hypos
          simpa [h] using hycont.comp continuous_subtype_val.continuousAt
      simpa [h] using hcont

end Section06
end Chap03
