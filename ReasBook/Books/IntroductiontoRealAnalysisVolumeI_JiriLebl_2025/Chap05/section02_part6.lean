/-
Authors: Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap02.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap03.section03
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section01
import IntroductiontoRealAnalysisVolumeI_JiriLebl_2025.Chap05.section02_part5

open Filter Topology
open scoped Matrix
open scoped BigOperators
open scoped Pointwise

section Chap05
section Section02

/-- On a degenerate interval, the upper/lower Darboux gap is zero. -/
lemma upper_lower_gap_degenerate_interval {a : ℝ} {h : ℝ → ℝ} :
    ∀ ε > 0, ∃ P : IntervalPartition a a,
      upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
  intro ε hε
  classical
  let P : IntervalPartition a a :=
    { n := 0
      points := fun _ => a
      mono := by
        simpa using (Subsingleton.strictMono (f := fun _ : Fin 1 => a))
      left_eq := rfl
      right_eq := by simp }
  have hgap0 : upperDarbouxSum h P - lowerDarbouxSum h P = 0 := by
    simp [upperDarbouxSum, lowerDarbouxSum, P]
  exact ⟨P, by simpa [hgap0] using hε⟩

/-- Gap estimate when the exceptional point is the left endpoint. -/
lemma upper_lower_gap_left_endpoint {a b c : ℝ} {h : ℝ → ℝ} {M : ℝ}
    (hc : c ∈ Set.Icc a b) (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0)
    (hM : ∀ x ∈ Set.Icc a b, |h x| ≤ M) (hhc : h c ≠ 0)
    (hca : c = a) (hlt : a < b) :
    ∀ ε > 0, ∃ P : IntervalPartition a b,
      upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
  classical
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, h x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  intro ε hε
  let δ : ℝ := min ((b - a) / 2) (ε / (4 * M))
  have hδpos : 0 < δ := by
    have h1 : 0 < (b - a) / 2 := by linarith
    have h2 : 0 < ε / (4 * M) := by
      have hMpos : 0 < M := by
        have hcpos : 0 < |h c| := abs_pos.mpr hhc
        have hle : |h c| ≤ M := hM c hc
        exact lt_of_lt_of_le hcpos hle
      exact div_pos hε (by nlinarith [hMpos])
    exact (lt_min_iff.mpr ⟨h1, h2⟩)
  have hδ_le : δ ≤ ε / (4 * M) := by
    exact min_le_right _ _
  have hδ_lt : a + δ < b := by
    have hδ_le' : δ ≤ (b - a) / 2 := min_le_left _ _
    linarith
  let P : IntervalPartition a b :=
    { n := 2
      points := ![a, a + δ, b]
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := ![a, a + δ, b])).2 ?_
        intro i
        fin_cases i <;> simp [hδpos, hδ_lt]
      left_eq := by simp
      right_eq := by simp }
  have hzero_right : ∀ x ∈ Set.Icc (a + δ) b, h x = 0 := by
    intro x hx
    have hxne : x ≠ c := by
      have hxgt : a + δ ≤ x := hx.1
      have hxne' : x ≠ a := by
        intro hx'
        have : a + δ ≤ a := by simpa [hx'] using hxgt
        linarith [hδpos]
      simpa [hca] using hxne'
    have hxIcc : x ∈ Set.Icc a b := ⟨le_trans (by linarith [hδpos]) hx.1, hx.2⟩
    have hx' : x ∈ Set.Icc a b \ {c} := by
      refine ⟨hxIcc, ?_⟩
      simpa [Set.mem_singleton_iff] using hxne
    exact hz x hx'
  have htag_right :
      upperTag h P ⟨1, by simp [P]⟩ = 0 ∧
        lowerTag h P ⟨1, by simp [P]⟩ = 0 := by
    have himage : h '' Set.Icc (a + δ) b = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [hzero_right x hx]
      · intro hy
        have : y = 0 := by simpa using hy
        subst this
        refine ⟨a + δ, ?_, ?_⟩
        · exact ⟨le_rfl, le_of_lt hδ_lt⟩
        · simpa using hzero_right (a + δ) ⟨le_rfl, le_of_lt hδ_lt⟩
    constructor <;> simp [upperTag, lowerTag, P, himage]
  have hdelta0 : P.delta ⟨0, by simp [P]⟩ = δ := by
    simp [IntervalPartition.delta, P]
  have hgap0 :
      upperDarbouxSum h P - lowerDarbouxSum h P ≤ 2 * M * δ := by
    have htag0 :
        upperTag h P ⟨0, by simp [P]⟩ - lowerTag h P ⟨0, by simp [P]⟩ ≤ 2 * M := by
      exact tag_gap_le_two_M (P := P) (i := ⟨0, by simp [P]⟩) hmin hmax
    exact upper_lower_gap_two_steps_right_zero (P := P) (M := M) (δ := δ) (hP := by simp [P])
      htag_right htag0 hdelta0
  have hgap' : upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
    have hMpos : 0 < M := by
      have hcpos : 0 < |h c| := abs_pos.mpr hhc
      have hle : |h c| ≤ M := hM c hc
      exact lt_of_lt_of_le hcpos hle
    exact gap_lt_of_le_twoM_delta (α := upperDarbouxSum h P - lowerDarbouxSum h P)
      hMpos hδ_le hgap0 hε
  exact ⟨P, hgap'⟩

/-- Gap estimate when the exceptional point is the right endpoint. -/
lemma upper_lower_gap_right_endpoint {a b c : ℝ} {h : ℝ → ℝ} {M : ℝ}
    (hc : c ∈ Set.Icc a b) (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0)
    (hM : ∀ x ∈ Set.Icc a b, |h x| ≤ M) (hhc : h c ≠ 0)
    (hcb : c = b) (hlt : a < b) :
    ∀ ε > 0, ∃ P : IntervalPartition a b,
      upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
  classical
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, h x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  intro ε hε
  let δ : ℝ := min ((b - a) / 2) (ε / (4 * M))
  have hδpos : 0 < δ := by
    have h1 : 0 < (b - a) / 2 := by linarith
    have h2 : 0 < ε / (4 * M) := by
      have hMpos : 0 < M := by
        have hcpos : 0 < |h c| := abs_pos.mpr hhc
        have hle : |h c| ≤ M := hM c hc
        exact lt_of_lt_of_le hcpos hle
      exact div_pos hε (by nlinarith [hMpos])
    exact (lt_min_iff.mpr ⟨h1, h2⟩)
  have hδ_le : δ ≤ ε / (4 * M) := by
    exact min_le_right _ _
  have hδ_lt : a < b - δ := by
    have hδ_le' : δ ≤ (b - a) / 2 := min_le_left _ _
    linarith
  let P : IntervalPartition a b :=
    { n := 2
      points := ![a, b - δ, b]
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := ![a, b - δ, b])).2 ?_
        intro i
        fin_cases i <;> simp [hδpos, hδ_lt]
      left_eq := by simp
      right_eq := by simp }
  have hzero_left : ∀ x ∈ Set.Icc a (b - δ), h x = 0 := by
    intro x hx
    have hxne : x ≠ c := by
      have hxlt : x < b := lt_of_le_of_lt hx.2 (by linarith)
      simpa [hcb] using ne_of_lt hxlt
    have hxIcc : x ∈ Set.Icc a b := ⟨hx.1, le_trans hx.2 (by linarith)⟩
    have hx' : x ∈ Set.Icc a b \ {c} := by
      refine ⟨hxIcc, ?_⟩
      simpa [Set.mem_singleton_iff] using hxne
    exact hz x hx'
  have htag_left :
      upperTag h P ⟨0, by simp [P]⟩ = 0 ∧
        lowerTag h P ⟨0, by simp [P]⟩ = 0 := by
    have himage : h '' Set.Icc a (b - δ) = {0} := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        simp [hzero_left x hx]
      · intro hy
        have : y = 0 := by simpa using hy
        subst this
        refine ⟨a, ?_, ?_⟩
        · exact ⟨le_rfl, le_of_lt hδ_lt⟩
        · simpa using hzero_left a ⟨le_rfl, le_of_lt hδ_lt⟩
    constructor <;> simp [upperTag, lowerTag, P, himage]
  have hdelta1 : P.delta ⟨1, by simp [P]⟩ = δ := by
    simp [IntervalPartition.delta, P]
  have hgap0 :
      upperDarbouxSum h P - lowerDarbouxSum h P ≤ 2 * M * δ := by
    have htag1 :
        upperTag h P ⟨1, by simp [P]⟩ - lowerTag h P ⟨1, by simp [P]⟩ ≤ 2 * M := by
      exact tag_gap_le_two_M (P := P) (i := ⟨1, by simp [P]⟩) hmin hmax
    exact upper_lower_gap_two_steps_left_zero (P := P) (M := M) (δ := δ) (hP := by simp [P])
      htag_left htag1 hdelta1
  have hgap' : upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
    have hMpos : 0 < M := by
      have hcpos : 0 < |h c| := abs_pos.mpr hhc
      have hle : |h c| ≤ M := hM c hc
      exact lt_of_lt_of_le hcpos hle
    exact gap_lt_of_le_twoM_delta (α := upperDarbouxSum h P - lowerDarbouxSum h P)
      hMpos hδ_le hgap0 hε
  exact ⟨P, hgap'⟩

/-- If `h` vanishes on a subinterval, its upper/lower tags are zero. -/
lemma upper_lower_gap_tag_zero_of_eq_zero {a b : ℝ} {h : ℝ → ℝ}
    (P : IntervalPartition a b) (i : Fin P.n)
    (hzero : ∀ x ∈ Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ), h x = 0) :
    upperTag h P i = 0 ∧ lowerTag h P i = 0 := by
  have himage :
      h '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) = {0} := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp [hzero x hx]
    · intro hy
      have : y = 0 := by simpa using hy
      subst this
      refine ⟨P.points (Fin.castSucc i), ?_, ?_⟩
      · exact ⟨le_rfl, le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))⟩
      · have hx :
            P.points (Fin.castSucc i) ∈
              Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
          exact ⟨le_rfl, le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))⟩
        simp [hzero _ hx]
  constructor <;> simp [upperTag, lowerTag, himage]

/-- Choose a small `δ` for the middle-case split. -/
lemma upper_lower_gap_middle_delta {a b c M ε : ℝ}
    (hMpos : 0 < M) (hca' : a < c) (hcb' : c < b) (hε : 0 < ε) :
    ∃ δ > 0,
      δ ≤ ε / (8 * M) ∧
      a < c - δ ∧ c - δ < c ∧ c < c + δ ∧ c + δ < b := by
  let δ : ℝ :=
    min ((c - a) / 2) (min ((b - c) / 2) (ε / (8 * M)))
  have hδpos : 0 < δ := by
    have h1 : 0 < (c - a) / 2 := by linarith [hca']
    have h2 : 0 < (b - c) / 2 := by linarith [hcb']
    have h3 : 0 < ε / (8 * M) := by
      exact div_pos hε (by nlinarith [hMpos])
    exact (lt_min_iff.mpr ⟨h1, (lt_min_iff.mpr ⟨h2, h3⟩)⟩)
  have hδ_eps : δ ≤ ε / (8 * M) := by
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hδ_left : δ ≤ (c - a) / 2 := min_le_left _ _
  have hδ_right : δ ≤ (b - c) / 2 := by
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hleft_lt : a < c - δ := by linarith [hδ_left, hca']
  have hright_lt : c - δ < c := by linarith [hδpos]
  have hmid_lt : c < c + δ := by linarith [hδpos]
  have hright2_lt : c + δ < b := by linarith [hδ_right, hcb']
  exact ⟨δ, hδpos, hδ_eps, hleft_lt, hright_lt, hmid_lt, hright2_lt⟩

/-- `h` vanishes on the left subinterval in the middle-case split. -/
lemma upper_lower_gap_middle_zero_left {a b c δ : ℝ} {h : ℝ → ℝ}
    (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0)
    (hright_lt : c - δ < c) (hcb' : c < b) :
    ∀ x ∈ Set.Icc a (c - δ), h x = 0 := by
  intro x hx
  have hxne : x ≠ c := by
    have hxlt : x < c := lt_of_le_of_lt hx.2 hright_lt
    exact ne_of_lt hxlt
  have hxIcc : x ∈ Set.Icc a b := by
    refine ⟨hx.1, le_trans hx.2 (le_of_lt (lt_trans hright_lt hcb'))⟩
  have hx' : x ∈ Set.Icc a b \ {c} := by
    refine ⟨hxIcc, ?_⟩
    simpa [Set.mem_singleton_iff] using hxne
  exact hz x hx'

/-- `h` vanishes on the right subinterval in the middle-case split. -/
lemma upper_lower_gap_middle_zero_right {a b c δ : ℝ} {h : ℝ → ℝ}
    (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0)
    (hca' : a < c) (hmid_lt : c < c + δ) :
    ∀ x ∈ Set.Icc (c + δ) b, h x = 0 := by
  intro x hx
  have hxne : x ≠ c := by
    intro hx'
    have : c + δ ≤ c := by simpa [hx'] using hx.1
    linarith [hmid_lt]
  have hxIcc : x ∈ Set.Icc a b := by
    refine ⟨?_, hx.2⟩
    have hca : a ≤ c := le_of_lt hca'
    have hccδ : c ≤ c + δ := le_of_lt hmid_lt
    exact le_trans hca (le_trans hccδ hx.1)
  have hx' : x ∈ Set.Icc a b \ {c} := by
    refine ⟨hxIcc, ?_⟩
    simpa [Set.mem_singleton_iff] using hxne
  exact hz x hx'

/-- Append two partitions and combine `2 * M * δ` gap bounds. -/
lemma upper_lower_gap_append_gap {a b c : ℝ} {h : ℝ → ℝ} {M δ : ℝ}
    (P1 : IntervalPartition a c) (P2 : IntervalPartition c b)
    (hgap1 : upperDarbouxSum h P1 - lowerDarbouxSum h P1 ≤ 2 * M * δ)
    (hgap2 : upperDarbouxSum h P2 - lowerDarbouxSum h P2 ≤ 2 * M * δ) :
    ∃ P : IntervalPartition a b,
      upperDarbouxSum h P - lowerDarbouxSum h P ≤ 4 * M * δ := by
  rcases intervalPartition_append (f := h) P1 P2 with ⟨P, _, hsum_lower, hsum_upper⟩
  have hsum_upper' :
      upperDarbouxSum h P = upperDarbouxSum h P1 + upperDarbouxSum h P2 := hsum_upper
  have hsum_lower' :
      lowerDarbouxSum h P = lowerDarbouxSum h P1 + lowerDarbouxSum h P2 := hsum_lower
  have hgapP :
      upperDarbouxSum h P - lowerDarbouxSum h P ≤ 4 * M * δ := by
    calc
      upperDarbouxSum h P - lowerDarbouxSum h P
          = (upperDarbouxSum h P1 - lowerDarbouxSum h P1) +
              (upperDarbouxSum h P2 - lowerDarbouxSum h P2) := by
                simp [hsum_upper', hsum_lower', sub_eq_add_neg, add_comm, add_left_comm,
                  add_assoc]
      _ ≤ 2 * M * δ + 2 * M * δ := add_le_add hgap1 hgap2
      _ = 4 * M * δ := by ring
  exact ⟨P, hgapP⟩

/-- Gap estimate when the exceptional point lies strictly inside `(a, b)`. -/
lemma upper_lower_gap_middle {a b c : ℝ} {h : ℝ → ℝ} {M : ℝ}
    (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0) (hM : ∀ x ∈ Set.Icc a b, |h x| ≤ M)
    (hhc : h c ≠ 0) (hca' : a < c) (hcb' : c < b) :
    ∀ ε > 0, ∃ P : IntervalPartition a b,
      upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
  classical
  have hc : c ∈ Set.Icc a b := ⟨le_of_lt hca', le_of_lt hcb'⟩
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, h x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  have hmin_ac : ∀ x ∈ Set.Icc a c, -M ≤ h x := by
    intro x hx
    exact hmin x ⟨hx.1, le_trans hx.2 (le_of_lt hcb')⟩
  have hmax_ac : ∀ x ∈ Set.Icc a c, h x ≤ M := by
    intro x hx
    exact hmax x ⟨hx.1, le_trans hx.2 (le_of_lt hcb')⟩
  have hmin_cb : ∀ x ∈ Set.Icc c b, -M ≤ h x := by
    intro x hx
    exact hmin x ⟨le_trans (le_of_lt hca') hx.1, hx.2⟩
  have hmax_cb : ∀ x ∈ Set.Icc c b, h x ≤ M := by
    intro x hx
    exact hmax x ⟨le_trans (le_of_lt hca') hx.1, hx.2⟩
  intro ε hε
  have hMpos : 0 < M := by
    have hcpos : 0 < |h c| := abs_pos.mpr hhc
    have hle : |h c| ≤ M := hM c hc
    exact lt_of_lt_of_le hcpos hle
  obtain ⟨δ, hδpos, hδ_eps, hleft_lt, hright_lt, hmid_lt, hright2_lt⟩ :=
    upper_lower_gap_middle_delta (M := M) (ε := ε) hMpos hca' hcb' hε
  let P1 : IntervalPartition a c :=
    { n := 2
      points := ![a, c - δ, c]
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := ![a, c - δ, c])).2 ?_
        intro i
        fin_cases i <;> simp [hleft_lt, hright_lt]
      left_eq := by simp
      right_eq := by simp }
  let P2 : IntervalPartition c b :=
    { n := 2
      points := ![c, c + δ, b]
      mono := by
        refine (Fin.strictMono_iff_lt_succ (f := ![c, c + δ, b])).2 ?_
        intro i
        fin_cases i <;> simp [hmid_lt, hright2_lt]
      left_eq := by simp
      right_eq := by simp }
  have hzero_left : ∀ x ∈ Set.Icc a (c - δ), h x = 0 :=
    upper_lower_gap_middle_zero_left (a := a) (b := b) (c := c) (δ := δ) (h := h)
      hz hright_lt hcb'
  have hzero_right : ∀ x ∈ Set.Icc (c + δ) b, h x = 0 :=
    upper_lower_gap_middle_zero_right (a := a) (b := b) (c := c) (δ := δ) (h := h)
      hz hca' hmid_lt
  have htag_left :
      upperTag h P1 ⟨0, by simp [P1]⟩ = 0 ∧
        lowerTag h P1 ⟨0, by simp [P1]⟩ = 0 := by
    refine upper_lower_gap_tag_zero_of_eq_zero (P := P1) (i := ⟨0, by simp [P1]⟩) ?_
    intro x hx
    have hx' : x ∈ Set.Icc a (c - δ) := by simpa [P1] using hx
    exact hzero_left x hx'
  have htag_right :
      upperTag h P2 ⟨1, by simp [P2]⟩ = 0 ∧
        lowerTag h P2 ⟨1, by simp [P2]⟩ = 0 := by
    refine upper_lower_gap_tag_zero_of_eq_zero (P := P2) (i := ⟨1, by simp [P2]⟩) ?_
    intro x hx
    have hx' : x ∈ Set.Icc (c + δ) b := by simpa [P2] using hx
    exact hzero_right x hx'
  have hdelta1 : P1.delta ⟨1, by simp [P1]⟩ = δ := by
    simp [IntervalPartition.delta, P1]
  have hdelta2 : P2.delta ⟨0, by simp [P2]⟩ = δ := by
    simp [IntervalPartition.delta, P2]
  have hgap1 :
      upperDarbouxSum h P1 - lowerDarbouxSum h P1 ≤ 2 * M * δ := by
    have htag1 :
        upperTag h P1 ⟨1, by simp [P1]⟩ - lowerTag h P1 ⟨1, by simp [P1]⟩ ≤ 2 * M := by
      exact tag_gap_le_two_M (P := P1) (i := ⟨1, by simp [P1]⟩) hmin_ac hmax_ac
    exact upper_lower_gap_two_steps_left_zero (P := P1) (M := M) (δ := δ) (hP := by simp [P1])
      htag_left htag1 hdelta1
  have hgap2 :
      upperDarbouxSum h P2 - lowerDarbouxSum h P2 ≤ 2 * M * δ := by
    have htag0 :
        upperTag h P2 ⟨0, by simp [P2]⟩ - lowerTag h P2 ⟨0, by simp [P2]⟩ ≤ 2 * M := by
      exact tag_gap_le_two_M (P := P2) (i := ⟨0, by simp [P2]⟩) hmin_cb hmax_cb
    exact upper_lower_gap_two_steps_right_zero (P := P2) (M := M) (δ := δ) (hP := by simp [P2])
      htag_right htag0 hdelta2
  obtain ⟨P, hgapP⟩ :=
    upper_lower_gap_append_gap (P1 := P1) (P2 := P2) (M := M) (δ := δ) hgap1 hgap2
  have hgap' : upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
    exact gap_lt_of_le_fourM_delta (α := upperDarbouxSum h P - lowerDarbouxSum h P)
      hMpos hδ_eps hgapP hε
  exact ⟨P, hgap'⟩

lemma upper_lower_gap_of_eq_zero_off_singleton {a b : ℝ} {h : ℝ → ℝ} {c : ℝ} {M : ℝ}
    (hc : c ∈ Set.Icc a b) (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0)
    (hM : ∀ x ∈ Set.Icc a b, |h x| ≤ M) (hhc : h c ≠ 0) :
    ∀ ε > 0, ∃ P : IntervalPartition a b,
      upperDarbouxSum h P - lowerDarbouxSum h P < ε := by
  classical
  have hab : a ≤ b := le_trans hc.1 hc.2
  intro ε hε
  by_cases hca : c = a
  · by_cases hlt : a < b
    · exact upper_lower_gap_left_endpoint (a := a) (b := b) (c := c) (h := h) (M := M)
        hc hz hM hhc hca hlt ε hε
    · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
      subst hEq
      exact upper_lower_gap_degenerate_interval (a := a) (h := h) ε hε
  · by_cases hcb : c = b
    · by_cases hlt : a < b
      · exact upper_lower_gap_right_endpoint (a := a) (b := b) (c := c) (h := h) (M := M)
          hc hz hM hhc hcb hlt ε hε
      · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
        subst hEq
        exact upper_lower_gap_degenerate_interval (a := a) (h := h) ε hε
    · have hca' : a < c := lt_of_le_of_ne hc.1 (by exact fun a_1 ↦ hca (id (Eq.symm a_1)))
      have hcb' : c < b := lt_of_le_of_ne hc.2 hcb
      exact upper_lower_gap_middle (a := a) (b := b) (c := c) (h := h) (M := M)
        hz hM hhc hca' hcb' ε hε

lemma lower_upper_sum_sign_of_eq_zero_off_singleton {a b : ℝ} {h : ℝ → ℝ} {c : ℝ} {M : ℝ}
    (hM : ∀ x ∈ Set.Icc a b, |h x| ≤ M)
    (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0) :
    ∀ P : IntervalPartition a b, lowerDarbouxSum h P ≤ 0 ∧ 0 ≤ upperDarbouxSum h P := by
  classical
  have hmin : ∀ x ∈ Set.Icc a b, -M ≤ h x := by
    intro x hx
    exact (abs_le.mp (hM x hx)).1
  have hmax : ∀ x ∈ Set.Icc a b, h x ≤ M := by
    intro x hx
    exact (abs_le.mp (hM x hx)).2
  intro P
  have hsub : ∀ i : Fin P.n,
      (0 : ℝ) ∈ h '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) := by
    intro i
    let left := P.points (Fin.castSucc i)
    let right := P.points i.succ
    have hlt : left < right := P.mono (Fin.castSucc_lt_succ (i := i))
    by_cases hleft : left = c
    · have hright_ne : right ≠ c := by
        exact ne_of_gt (by simpa [hleft] using hlt)
      have hx : right ∈ Set.Icc left right := ⟨le_of_lt hlt, le_rfl⟩
      have hmono : Monotone P.points := P.mono.monotone
      have hleft_le : a ≤ left := by
        have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
        simpa [P.left_eq] using h0
      have hright_le : right ≤ b := by
        have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
        simpa [P.right_eq, Fin.last] using hlast
      have hright_mem : right ∈ Set.Icc a b :=
        ⟨le_trans hleft_le hx.1, le_trans hx.2 hright_le⟩
      have hx' : right ∈ Set.Icc a b \ {c} := by
        refine ⟨hright_mem, ?_⟩
        simpa [Set.mem_singleton_iff] using hright_ne
      have hright0 : h right = 0 := hz right hx'
      exact ⟨right, hx, by simp [hright0]⟩
    · have hx : left ∈ Set.Icc left right := ⟨le_rfl, le_of_lt hlt⟩
      have hmono : Monotone P.points := P.mono.monotone
      have hleft_le : a ≤ left := by
        have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
        simpa [P.left_eq] using h0
      have hright_le : right ≤ b := by
        have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
        simpa [P.right_eq, Fin.last] using hlast
      have hleft_mem : left ∈ Set.Icc a b :=
        ⟨hleft_le, le_trans (le_of_lt hlt) hright_le⟩
      have hx' : left ∈ Set.Icc a b \ {c} := by
        refine ⟨hleft_mem, ?_⟩
        simpa [Set.mem_singleton_iff] using hleft
      have hleft0 : h left = 0 := hz left hx'
      exact ⟨left, hx, by simp [hleft0]⟩
  have hle_term :
      ∀ i : Fin P.n, lowerTag h P i * P.delta i ≤ 0 := by
    intro i
    have hBddBelow :
        BddBelow (h '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
      refine ⟨-M, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hmono : Monotone P.points := P.mono.monotone
      have hleft_le : a ≤ P.points (Fin.castSucc i) := by
        have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
        simpa [P.left_eq] using h0
      have hright_le : P.points i.succ ≤ b := by
        have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
        simpa [P.right_eq, Fin.last] using hlast
      have hxIcc : x ∈ Set.Icc a b :=
        ⟨le_trans hleft_le hx.1, le_trans hx.2 hright_le⟩
      exact hmin x hxIcc
    have hle_tag :
        lowerTag h P i ≤ 0 := by
      exact csInf_le hBddBelow (hsub i)
    have hdelta_nonneg : 0 ≤ P.delta i := by
      exact le_of_lt (sub_pos.mpr (P.mono (Fin.castSucc_lt_succ (i := i))))
    exact mul_nonpos_of_nonpos_of_nonneg hle_tag hdelta_nonneg
  have hge_term :
      ∀ i : Fin P.n, 0 ≤ upperTag h P i * P.delta i := by
    intro i
    have hBddAbove :
        BddAbove (h '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)) := by
      refine ⟨M, ?_⟩
      intro y hy
      rcases hy with ⟨x, hx, rfl⟩
      have hmono : Monotone P.points := P.mono.monotone
      have hleft_le : a ≤ P.points (Fin.castSucc i) := by
        have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono (Fin.zero_le _)
        simpa [P.left_eq] using h0
      have hright_le : P.points i.succ ≤ b := by
        have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono (Fin.le_last _)
        simpa [P.right_eq, Fin.last] using hlast
      have hxIcc : x ∈ Set.Icc a b :=
        ⟨le_trans hleft_le hx.1, le_trans hx.2 hright_le⟩
      exact hmax x hxIcc
    have hge_tag :
        0 ≤ upperTag h P i := by
      exact le_csSup hBddAbove (hsub i)
    have hdelta_nonneg : 0 ≤ P.delta i := by
      exact le_of_lt (sub_pos.mpr (P.mono (Fin.castSucc_lt_succ (i := i))))
    exact mul_nonneg hge_tag hdelta_nonneg
  have hsum_le :
      lowerDarbouxSum h P ≤ 0 := by
    have hsum_le' :
        (∑ i : Fin P.n, lowerTag h P i * P.delta i) ≤
          ∑ i : Fin P.n, (0 : ℝ) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hle_term i
    simpa [lowerDarbouxSum] using hsum_le'
  have hsum_ge :
      0 ≤ upperDarbouxSum h P := by
    have hsum_ge' :
        (∑ i : Fin P.n, (0 : ℝ)) ≤
          ∑ i : Fin P.n, upperTag h P i * P.delta i := by
      refine Finset.sum_le_sum ?_
      intro i hi
      exact hge_term i
    simpa [upperDarbouxSum] using hsum_ge'
  exact ⟨hsum_le, hsum_ge⟩

/-- Changing a single point on `[a, b]` does not affect the Riemann integral. -/
lemma riemannIntegral_eq_zero_of_eq_zero_off_singleton {a b : ℝ} {h : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ Set.Icc a b) (hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0) :
    ∃ hh : RiemannIntegrableOn h a b, riemannIntegral h a b hh = 0 := by
  classical
  have hab : a ≤ b := le_trans hc.1 hc.2
  have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |h x| ≤ M := by
    refine ⟨|h c|, ?_⟩
    intro x hx
    by_cases hxc : x = c
    · simp [hxc]
    · have hx' : x ∈ Set.Icc a b \ {c} := by
        refine ⟨hx, ?_⟩
        simpa [Set.mem_singleton_iff] using hxc
      have hx0 : h x = 0 := hz x hx'
      simp [hx0]
  by_cases hhc : h c = 0
  · have hzero : ∀ x ∈ Set.Icc a b, h x = 0 := by
      intro x hx
      by_cases hxc : x = c
      · simp [hxc, hhc]
      · have hx' : x ∈ Set.Icc a b \ {c} := by
          refine ⟨hx, ?_⟩
          simpa [Set.mem_singleton_iff] using hxc
        exact hz x hx'
    exact riemannIntegral_eq_zero_of_eq_zero_on_Icc hab hzero
  · obtain ⟨M, hM⟩ := hbound
    have hgap :=
      upper_lower_gap_of_eq_zero_off_singleton (a := a) (b := b) (c := c) (h := h) (M := M)
        hc hz hM hhc
    have hh : RiemannIntegrableOn h a b :=
      riemannIntegrable_of_upper_lower_gap (f := h) (a := a) (b := b) ⟨M, hM⟩ hgap
    have hsum_sign :=
      lower_upper_sum_sign_of_eq_zero_off_singleton (a := a) (b := b) (c := c) (h := h) (M := M)
        hM hz
    have hnonempty_lower :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum h P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
      refine ⟨lowerDarbouxSum h P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hnonempty_upper :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum h P)).Nonempty := by
      obtain ⟨P0⟩ := intervalPartition_nonempty (a := a) (b := b) hab
      refine ⟨upperDarbouxSum h P0, ?_⟩
      exact ⟨P0, rfl⟩
    have hlower_le : lowerDarbouxIntegral h a b ≤ 0 := by
      have hle : ∀ y ∈ Set.range (fun P : IntervalPartition a b => lowerDarbouxSum h P), y ≤ 0 := by
        intro y hy
        rcases hy with ⟨P, rfl⟩
        exact (hsum_sign P).1
      have hsup :
          sSup (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum h P)) ≤ 0 :=
        csSup_le hnonempty_lower hle
      simpa [lowerDarbouxIntegral] using hsup
    have hupper_ge : 0 ≤ upperDarbouxIntegral h a b := by
      have hge : ∀ y ∈ Set.range (fun P : IntervalPartition a b => upperDarbouxSum h P), 0 ≤ y := by
        intro y hy
        rcases hy with ⟨P, rfl⟩
        exact (hsum_sign P).2
      have hinf :
          0 ≤ sInf (Set.range (fun P : IntervalPartition a b => upperDarbouxSum h P)) :=
        le_csInf hnonempty_upper hge
      simpa [upperDarbouxIntegral] using hinf
    have hEq : lowerDarbouxIntegral h a b = upperDarbouxIntegral h a b := hh.2
    have h0 : lowerDarbouxIntegral h a b = 0 := by
      linarith [hlower_le, hupper_ge, hEq]
    refine ⟨hh, ?_⟩
    simp [riemannIntegral, h0]

/-- Changing a single point on `[a, b]` does not affect the Riemann integral. -/
lemma riemannIntegral_eq_of_eq_off_singleton {a b : ℝ} {f g : ℝ → ℝ} {c : ℝ}
    (hc : c ∈ Set.Icc a b) (hf : RiemannIntegrableOn f a b)
    (hfg : ∀ x ∈ Set.Icc a b \ {c}, g x = f x) :
    ∃ hg : RiemannIntegrableOn g a b,
      riemannIntegral g a b hg = riemannIntegral f a b hf := by
  classical
  let h : ℝ → ℝ := fun x => if x = c then g x - f x else 0
  have hz : ∀ x ∈ Set.Icc a b \ {c}, h x = 0 := by
    intro x hx
    have hxc : x ≠ c := by
      simpa [Set.mem_singleton_iff] using hx.2
    simp [h, hxc]
  have hfg' : ∀ x ∈ Set.Icc a b, g x = f x + h x := by
    intro x hx
    by_cases hxc : x = c
    · simp [h, hxc]
    · have hx' : x ∈ Set.Icc a b \ {c} := by
        refine ⟨hx, ?_⟩
        simpa [Set.mem_singleton_iff] using hxc
      have hxfg : g x = f x := hfg x hx'
      simp [h, hxc, hxfg]
  obtain ⟨hh, hEq0⟩ :=
    riemannIntegral_eq_zero_of_eq_zero_off_singleton (a := a) (b := b) (c := c) hc hz
  obtain ⟨hfg_int, hsum_eq⟩ :=
    (riemannIntegral_linearity (a := a) (b := b) (α := (1 : ℝ)) (f := f) (g := h) hf hh).2
  obtain ⟨hg, hEqg⟩ := riemannIntegral_congr_on_Icc hfg' hfg_int
  refine ⟨hg, ?_⟩
  calc
    riemannIntegral g a b hg = riemannIntegral (fun x => f x + h x) a b hfg_int := hEqg
    _ = riemannIntegral f a b hf + riemannIntegral h a b hh := hsum_eq
    _ = riemannIntegral f a b hf := by simp [hEq0]

/-- Proposition 5.2.10: If `f : [a, b] → ℝ` is Riemann integrable and `g` agrees
with `f` on `[a, b]` except on a finite set `S`, then `g` is Riemann integrable
and the integrals of `f` and `g` over `[a, b]` coincide. -/
theorem riemannIntegral_eq_of_eq_off_finite {a b : ℝ} {f g : ℝ → ℝ} {S : Set ℝ}
    (hf : RiemannIntegrableOn f a b) (hfin : S.Finite)
    (hfg : ∀ x ∈ Set.Icc a b \ S, g x = f x) :
    ∃ hg : RiemannIntegrableOn g a b,
      riemannIntegral g a b hg = riemannIntegral f a b hf := by
  classical
  let S' : Set ℝ := S ∩ Set.Icc a b
  have hfin' : S'.Finite := by
    refine hfin.subset ?_
    intro x hx
    have hx' : x ∈ S ∩ Set.Icc a b := by
      simpa [S'] using hx
    exact hx'.1
  have hfg' : ∀ x ∈ Set.Icc a b \ S', g x = f x := by
    intro x hx
    have hxS : x ∉ S := by
      intro hxS
      apply hx.2
      have hx' : x ∈ S ∩ Set.Icc a b := ⟨hxS, hx.1⟩
      simpa [S'] using hx'
    exact hfg x ⟨hx.1, hxS⟩
  have hsubset : S' ⊆ Set.Icc a b := by
    intro x hx
    have hx' : x ∈ S ∩ Set.Icc a b := by
      simpa [S'] using hx
    exact hx'.2
  have main :
      ∀ {T : Set ℝ}, T.Finite →
        (∀ {g : ℝ → ℝ}, T ⊆ Set.Icc a b →
          (∀ x ∈ Set.Icc a b \ T, g x = f x) →
          ∃ hg : RiemannIntegrableOn g a b,
            riemannIntegral g a b hg = riemannIntegral f a b hf) := by
    intro T hT
    classical
    refine Set.Finite.induction_on (s := T) (hs := hT)
      (motive := fun T : Set ℝ => fun _ =>
        ∀ {g : ℝ → ℝ}, T ⊆ Set.Icc a b →
          (∀ x ∈ Set.Icc a b \ T, g x = f x) →
          ∃ hg : RiemannIntegrableOn g a b,
            riemannIntegral g a b hg = riemannIntegral f a b hf) ?_ ?_
    · intro g hTsub hfgT
      have hfgIcc : ∀ x ∈ Set.Icc a b, g x = f x := by
        intro x hx
        have hx' : x ∈ Set.Icc a b \ (∅ : Set ℝ) := by
          exact ⟨hx, by simp⟩
        exact hfgT x hx'
      exact riemannIntegral_congr_on_Icc hfgIcc hf
    · intro c T hc hTfin hIH g hTsub hfgT
      have hcIcc : c ∈ Set.Icc a b := by
        exact hTsub (by simp)
      have hsubsetT : T ⊆ Set.Icc a b := by
        intro x hx
        exact hTsub (Set.mem_insert_of_mem c hx)
      let g' : ℝ → ℝ := fun x => if x = c then f x else g x
      have hfg' : ∀ x ∈ Set.Icc a b \ T, g' x = f x := by
        intro x hx
        by_cases hxc : x = c
        · simp [g', hxc]
        · have hx' : x ∈ Set.Icc a b \ insert c T := by
            refine ⟨hx.1, ?_⟩
            intro hxins
            rcases (by simpa [Set.mem_insert_iff] using hxins) with hxc' | hxT
            · exact hxc hxc'
            · exact hx.2 hxT
          have hxfg : g x = f x := hfgT x hx'
          simp [g', hxc, hxfg]
      obtain ⟨hg', hEq'⟩ := hIH (g := g') hsubsetT hfg'
      have hgg' : ∀ x ∈ Set.Icc a b \ ({c} : Set ℝ), g x = g' x := by
        intro x hx
        have hxc : x ≠ c := by
          simpa using hx.2
        simp [g', hxc]
      obtain ⟨hg, hEqg⟩ :=
        riemannIntegral_eq_of_eq_off_singleton (a := a) (b := b)
          (f := g') (g := g) (c := c) hcIcc hg' hgg'
      refine ⟨hg, ?_⟩
      calc
        riemannIntegral g a b hg = riemannIntegral g' a b hg' := hEqg
        _ = riemannIntegral f a b hf := hEq'
  have hmain := main (T := S') hfin' (g := g) hsubset hfg'
  exact hmain

/-- Proposition 5.2.11: A monotone function `f : [a, b] → ℝ` belongs to
`ℛ([a, b])`, i.e., it is Riemann integrable on the closed interval `[a, b]`. -/
lemma monotoneOn_riemannIntegrableOn {a b : ℝ} {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Icc a b)) :
    RiemannIntegrableOn f a b := by
  classical
  by_cases hab : a ≤ b
  · set M : ℝ := max (|f a|) (|f b|) with hM
    have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
      refine ⟨M, ?_⟩
      intro x hx
      have hax : f a ≤ f x := hmono ⟨le_rfl, hab⟩ hx hx.1
      have hxb : f x ≤ f b := hmono hx ⟨hab, le_rfl⟩ hx.2
      have hfa : |f a| ≤ M := by
        simp [hM]
      have hfb : |f b| ≤ M := by
        simp [hM]
      have hfa' : -M ≤ f a ∧ f a ≤ M := abs_le.mp hfa
      have hfb' : -M ≤ f b ∧ f b ≤ M := abs_le.mp hfb
      have hlow : -M ≤ f x := le_trans hfa'.1 hax
      have hhigh : f x ≤ M := le_trans hxb hfb'.2
      exact abs_le.mpr ⟨hlow, hhigh⟩
    have hgap :
        ∀ ε > 0, ∃ P : IntervalPartition a b,
          upperDarbouxSum f P - lowerDarbouxSum f P < ε := by
      intro ε hε
      by_cases hlt : a < b
      · have hfa_le_fb : f a ≤ f b := hmono ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
        set D : ℝ := f b - f a
        have hD_nonneg : 0 ≤ D := by
          dsimp [D]
          linarith [hfa_le_fb]
        have hDpos : 0 < D + 1 := by
          linarith [hD_nonneg]
        set δ : ℝ := ε / (D + 1) with hδ
        have hδpos : 0 < δ := by
          exact div_pos hε hDpos
        obtain ⟨P, hdelta⟩ := intervalPartition_small_delta (a := a) (b := b) hlt hδpos
        have subinterval_subset (P : IntervalPartition a b) (i : Fin P.n) :
            Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ) ⊆ Set.Icc a b := by
          intro x hx
          rcases hx with ⟨hx1, hx2⟩
          have hmono' : Monotone P.points := P.mono.monotone
          have hleft : a ≤ P.points (Fin.castSucc i) := by
            have h0 : P.points 0 ≤ P.points (Fin.castSucc i) := hmono' (Fin.zero_le _)
            simpa [P.left_eq] using h0
          have hright : P.points i.succ ≤ b := by
            have hlast : P.points i.succ ≤ P.points (Fin.last P.n) := hmono' (Fin.le_last _)
            simpa [P.right_eq, Fin.last] using hlast
          exact ⟨le_trans hleft hx1, le_trans hx2 hright⟩
        have htag_gap (i : Fin P.n) :
            upperTag f P i - lowerTag f P i ≤
              f (P.points i.succ) - f (P.points (Fin.castSucc i)) := by
          have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
            le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
          have hnonempty :
              (f '' Set.Icc (P.points (Fin.castSucc i)) (P.points i.succ)).Nonempty := by
            refine ⟨f (P.points (Fin.castSucc i)), ?_⟩
            exact ⟨P.points (Fin.castSucc i), ⟨le_rfl, hle⟩, rfl⟩
          have hlow :
              f (P.points (Fin.castSucc i)) ≤ lowerTag f P i := by
            refine le_csInf hnonempty ?_
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            have hxIcc : x ∈ Set.Icc a b := subinterval_subset P i hx
            have hleftIcc : P.points (Fin.castSucc i) ∈ Set.Icc a b :=
              subinterval_subset P i ⟨le_rfl, hle⟩
            exact hmono hleftIcc hxIcc hx.1
          have hupp :
              upperTag f P i ≤ f (P.points i.succ) := by
            refine csSup_le hnonempty ?_
            intro y hy
            rcases hy with ⟨x, hx, rfl⟩
            have hxIcc : x ∈ Set.Icc a b := subinterval_subset P i hx
            have hrightIcc : P.points i.succ ∈ Set.Icc a b :=
              subinterval_subset P i ⟨hle, le_rfl⟩
            exact hmono hxIcc hrightIcc hx.2
          linarith
        have hdelta_nonneg (i : Fin P.n) : 0 ≤ P.delta i := by
          exact le_of_lt (sub_pos.mpr (P.mono (Fin.castSucc_lt_succ (i := i))))
        have hdiff_nonneg (i : Fin P.n) :
            0 ≤ f (P.points i.succ) - f (P.points (Fin.castSucc i)) := by
          have hle : P.points (Fin.castSucc i) ≤ P.points i.succ :=
            le_of_lt (P.mono (Fin.castSucc_lt_succ (i := i)))
          have hleftIcc : P.points (Fin.castSucc i) ∈ Set.Icc a b :=
            subinterval_subset P i ⟨le_rfl, hle⟩
          have hrightIcc : P.points i.succ ∈ Set.Icc a b :=
            subinterval_subset P i ⟨hle, le_rfl⟩
          have hle' : f (P.points (Fin.castSucc i)) ≤ f (P.points i.succ) :=
            hmono hleftIcc hrightIcc hle
          linarith
        have hgap_le : upperDarbouxSum f P - lowerDarbouxSum f P ≤ δ * D := by
          have sum_succ_sub_castSucc : ∀ {n : ℕ} (g : Fin (n + 1) → ℝ),
              (∑ i : Fin n, (g i.succ - g (Fin.castSucc i))) =
                g (Fin.last n) - g 0 := by
            intro n g
            induction n with
            | zero =>
                simp
            | succ n ih =>
                have hsum :=
                  (Fin.sum_univ_succ (f := fun i : Fin (n + 1) =>
                    (g i.succ - g (Fin.castSucc i))))
                have hih :
                    (∑ i : Fin n,
                        (g (i.succ).succ - g (Fin.castSucc (i.succ)))) =
                      g (Fin.last (n + 1)) - g 1 := by
                  simpa using (ih (g := fun j : Fin (n + 1) => g j.succ))
                calc
                  (∑ i : Fin (n + 1), (g i.succ - g (Fin.castSucc i)))
                      = (g (Fin.succ 0) - g (Fin.castSucc 0)) +
                          ∑ i : Fin n,
                            (g (i.succ).succ - g (Fin.castSucc (i.succ))) := hsum
                  _ = (g (Fin.succ 0) - g (Fin.castSucc 0)) +
                      (g (Fin.last (n + 1)) - g 1) := by
                        rw [hih]
                  _ = (g 1 - g 0) + (g (Fin.last (n + 1)) - g 1) := by
                        simp
                  _ = g (Fin.last (n + 1)) - g 0 := by ring
          have hsum :
              upperDarbouxSum f P - lowerDarbouxSum f P =
                ∑ i : Fin P.n, (upperTag f P i - lowerTag f P i) * P.delta i := by
            calc
              upperDarbouxSum f P - lowerDarbouxSum f P =
                  ∑ i : Fin P.n,
                    (upperTag f P i * P.delta i - lowerTag f P i * P.delta i) := by
                      simp [upperDarbouxSum, lowerDarbouxSum, Finset.sum_sub_distrib]
              _ = ∑ i : Fin P.n, (upperTag f P i - lowerTag f P i) * P.delta i := by
                      refine Finset.sum_congr rfl ?_
                      intro i hi
                      ring
          have hsum_le :
              ∑ i : Fin P.n, (upperTag f P i - lowerTag f P i) * P.delta i ≤
                ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * P.delta i := by
            refine Finset.sum_le_sum ?_
            intro i hi
            exact mul_le_mul_of_nonneg_right (htag_gap i) (hdelta_nonneg i)
          have hsum_le' :
              ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * P.delta i ≤
                ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * δ := by
            refine Finset.sum_le_sum ?_
            intro i hi
            have hle : P.delta i ≤ δ := le_of_lt (hdelta i)
            exact mul_le_mul_of_nonneg_left hle (hdiff_nonneg i)
          have hmul_sum :
              ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * δ =
                δ * ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) := by
            simpa [mul_comm, mul_left_comm, mul_assoc] using
              (Finset.mul_sum (s := (Finset.univ : Finset (Fin P.n)))
                (f := fun i : Fin P.n =>
                  f (P.points i.succ) - f (P.points (Fin.castSucc i))) δ).symm
          have hsum_diff :
              ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) =
                f b - f a := by
            have h := sum_succ_sub_castSucc (g := fun j : Fin (P.n + 1) => f (P.points j))
            simpa [P.left_eq, P.right_eq, Fin.last] using h
          calc
            upperDarbouxSum f P - lowerDarbouxSum f P
                = ∑ i : Fin P.n, (upperTag f P i - lowerTag f P i) * P.delta i := hsum
            _ ≤ ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * P.delta i := hsum_le
            _ ≤ ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) * δ := hsum_le'
            _ = δ * ∑ i : Fin P.n,
                  (f (P.points i.succ) - f (P.points (Fin.castSucc i))) := hmul_sum
            _ = δ * (f b - f a) := by
                  simp [hsum_diff]
            _ = δ * D := by
                  simp [D]
        have hfrac : D / (D + 1) < 1 := by
          have hDlt : D < D + 1 := by linarith
          exact (div_lt_one hDpos).2 hDlt
        have hmul : ε * (D / (D + 1)) < ε := by
          simpa using (mul_lt_mul_of_pos_left hfrac hε)
        have hδ_mul : δ * D = ε * (D / (D + 1)) := by
          simp [hδ, div_eq_mul_inv, mul_comm, mul_left_comm]
        have hgap_lt : upperDarbouxSum f P - lowerDarbouxSum f P < ε := by
          have hδ_mul_lt : δ * D < ε := by
            simpa [hδ_mul] using hmul
          exact lt_of_le_of_lt hgap_le hδ_mul_lt
        exact ⟨P, hgap_lt⟩
      · have hEq : a = b := le_antisymm hab (not_lt.mp hlt)
        subst hEq
        let P : IntervalPartition a a :=
          { n := 0
            points := fun _ => a
            mono := by
              refine (Fin.strictMono_iff_lt_succ (f := fun _ : Fin (0 + 1) => a)).2 ?_
              intro i
              exact (Fin.elim0 i)
            left_eq := by simp
            right_eq := by simp }
        have hgap0 : upperDarbouxSum f P - lowerDarbouxSum f P = 0 := by
          simp [upperDarbouxSum, lowerDarbouxSum, P]
        refine ⟨P, ?_⟩
        simpa [hgap0] using hε
    exact riemannIntegrable_of_upper_lower_gap hbound hgap
  · have hbound : ∃ M : ℝ, ∀ x ∈ Set.Icc a b, |f x| ≤ M := by
      refine ⟨0, ?_⟩
      intro x hx
      have : a ≤ b := le_trans hx.1 hx.2
      exact (hab this).elim
    have hno_lower (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => lowerDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hno_upper (f' : ℝ → ℝ) :
        (Set.range (fun P : IntervalPartition a b => upperDarbouxSum f' P)) = ∅ := by
      ext y
      constructor
      · rintro ⟨P, rfl⟩
        have hmono : Monotone P.points := P.mono.monotone
        have h0 : P.points 0 ≤ P.points (Fin.last P.n) := hmono (Fin.zero_le _)
        have hPab : a ≤ b := by
          simpa [P.left_eq, P.right_eq, Fin.last] using h0
        exact (hab hPab).elim
      · intro hy
        cases hy
    have hEq :
        lowerDarbouxIntegral f a b = upperDarbouxIntegral f a b := by
      simp [lowerDarbouxIntegral, upperDarbouxIntegral, hno_lower, hno_upper]
    exact ⟨hbound, hEq⟩

end Section02
end Chap05
