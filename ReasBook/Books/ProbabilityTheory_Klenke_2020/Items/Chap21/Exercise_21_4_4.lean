/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_21
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Exercise_21_1_4

open MeasureTheory ProbabilityTheory Set Topology
open scoped NNReal ENNReal ProbabilityTheory

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u}
variable {E : Type v}

attribute [local instance] Classical.propDecidable

/-- The strictly positive first hitting time of `A` by `X`, with value `⊤` when the path never
enters `A` after time `0`. -/
def strictPositiveHittingTime (X : NNReal → Ω → E) (A : Set E) : Ω → WithTop NNReal :=
  fun ω ↦
    if _ : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A then
      ((sInf {t : NNReal | 0 < t ∧ X t ω ∈ A}) : NNReal)
    else
      ⊤

scoped notation:arg "τ_[" X ", " A "]" => strictPositiveHittingTime X A

/-- Helper for Exercise 21.4.4: `τ_[X, A] ω = ⊤` exactly when the path avoids `A` at every
strictly positive time. -/
theorem strictHittingTime_eq_top_iff
    (X : NNReal → Ω → E) (A : Set E) (ω : Ω) :
    (τ_[X, A]) ω = ⊤ ↔ ∀ t : NNReal, 0 < t → X t ω ∉ A := by
  by_cases h : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A
  · rcases h with ⟨t, ht, htA⟩
    have hHit : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A := ⟨t, ht, htA⟩
    constructor
    · intro hτ
      have hne :
          (((sInf {s : NNReal | 0 < s ∧ X s ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤ := by
        simpa using (WithTop.coe_ne_top :
          (((sInf {s : NNReal | 0 < s ∧ X s ω ∈ A}) : NNReal) : WithTop NNReal) ≠ ⊤)
      exact False.elim <| hne <| by simpa [strictPositiveHittingTime, hHit] using hτ
    · intro havoid
      exact False.elim (havoid t ht htA)
  · constructor
    · intro _ t ht htA
      exact h ⟨t, ht, htA⟩
    · intro _
      simp [strictPositiveHittingTime, h]

/-- Helper for Exercise 21.4.4: if the initial value starts outside `A`, then the strict-positive
hitting time agrees with `hittingAfter X A 0`. -/
theorem strictPositiveHittingTime_eq_hittingAfter_of_not_mem_zero
    (X : NNReal → Ω → E) (A : Set E) (ω : Ω) (h0 : X 0 ω ∉ A) :
    strictPositiveHittingTime X A ω = hittingAfter X A 0 ω := by
  by_cases hHit : ∃ t : NNReal, 0 < t ∧ X t ω ∈ A
  · have hHitAny : ∃ t : NNReal, X t ω ∈ A := by
      rcases hHit with ⟨t, -, htA⟩
      exact ⟨t, htA⟩
    have hSet :
        {t : NNReal | 0 < t ∧ X t ω ∈ A} = {t : NNReal | X t ω ∈ A} := by
      ext t
      constructor
      · intro ht
        exact ht.2
      · intro ht
        refine ⟨lt_of_le_of_ne (show (0 : NNReal) ≤ t by positivity) ?_, ht⟩
        intro hzero
        exact h0 <| by simpa [hzero] using ht
    simp [strictPositiveHittingTime, hittingAfter, hHit, hHitAny, hSet]
  · have hHitAny : ¬ ∃ t : NNReal, X t ω ∈ A := by
      rintro ⟨t, htA⟩
      by_cases ht0 : t = 0
      · exact h0 <| by simpa [ht0] using htA
      · exact hHit ⟨t, lt_of_le_of_ne (show (0 : NNReal) ≤ t by positivity) (Ne.symm ht0), htA⟩
    simp [strictPositiveHittingTime, hittingAfter, hHit, hHitAny]

/-- Helper for Exercise 21.4.4: `τ_[X, A] ω ≤ t` iff every later horizon `t + ε` contains a
strictly positive hit of `A`. -/
private theorem strictPositiveHittingTime_le_iff_forall_exists_lt
    {X : NNReal → Ω → E} {A : Set E} {ω : Ω} {t : NNReal} :
    strictPositiveHittingTime X A ω ≤ t ↔
      ∀ ε : NNReal, 0 < ε → ∃ s : NNReal, 0 < s ∧ X s ω ∈ A ∧ s < t + ε := by
  by_cases hHit : ∃ s : NNReal, 0 < s ∧ X s ω ∈ A
  · let S : Set NNReal := {s : NNReal | 0 < s ∧ X s ω ∈ A}
    have hS_nonempty : S.Nonempty := hHit
    have hS_bdd : BddBelow S := ⟨0, fun s hs ↦ hs.1.le⟩
    constructor
    · intro hτ ε hε
      have hsInf_lt : sInf S < t + ε := by
        have hsInf_le : sInf S ≤ t := by
          exact WithTop.coe_le_coe.mp <| by
            simpa [strictPositiveHittingTime, S, hHit] using hτ
        exact lt_of_le_of_lt hsInf_le (lt_add_of_pos_right _ hε)
      rcases exists_lt_of_csInf_lt hS_nonempty hsInf_lt with ⟨s, hsS, hs_lt⟩
      exact ⟨s, hsS.1, hsS.2, hs_lt⟩
    · intro happrox
      suffices hsInf_le : sInf S ≤ t by
        exact
          by
            simpa [strictPositiveHittingTime, S, hHit] using
              (WithTop.coe_le_coe.mpr hsInf_le :
                (((sInf S : NNReal) : WithTop NNReal) ≤ (t : WithTop NNReal)))
      by_contra hsInf_gt
      have hlt : t < sInf S := lt_of_not_ge hsInf_gt
      obtain ⟨r, htr, hrs⟩ := exists_between hlt
      have hε : 0 < r - t := tsub_pos_iff_lt.mpr htr
      obtain ⟨s, hs0, hsA, hs_lt⟩ := happrox (r - t) hε
      have hs_mem : s ∈ S := ⟨hs0, hsA⟩
      have hsInf_le_s : sInf S ≤ s := csInf_le hS_bdd hs_mem
      have hcontr : s < sInf S := by
        calc
          s < t + (r - t) := hs_lt
          _ = r := by rw [add_tsub_cancel_of_le htr.le]
          _ < sInf S := hrs
      exact (not_lt_of_ge hsInf_le_s) hcontr
  · constructor
    · intro hτ
      exfalso
      have htop : strictPositiveHittingTime X A ω = ⊤ := by
        simp [strictPositiveHittingTime, hHit]
      have ht_ne_top : ((t : NNReal) : WithTop NNReal) ≠ ⊤ := by
        rintro ⟨⟩
      exact ht_ne_top (top_le_iff.mp (by simpa [htop] using hτ))
    · intro happrox
      exfalso
      obtain ⟨s, hs0, hsA, -⟩ := happrox 1 (by norm_num)
      exact hHit ⟨s, hs0, hsA⟩

section Topological

variable [TopologicalSpace E]

/-- Helper for Exercise 21.4.4: after an open hit at time `s`, right continuity produces a
strictly positive rational hit before any later horizon `r`. -/
private theorem exists_nnrat_hit_lt_of_open_of_rightContinuous
    {X : NNReal → Ω → E} (hXrc : HasRightContinuousPaths X) {U : Set E} (hU : IsOpen U)
    {ω : Ω} {s r : NNReal} (hs0 : 0 < s) (hsr : s < r) (hsU : X s ω ∈ U) :
    ∃ q : ℚ≥0, 0 < q ∧ (q : NNReal) < r ∧ X q ω ∈ U := by
  have hPre :
      {t : NNReal | X t ω ∈ U} ∈ 𝓝[≥] s := by
    simpa using (hXrc ω s) (hU.mem_nhds hsU)
  rcases (mem_nhdsGE_iff_exists_mem_Ioc_Ico_subset hsr).1 hPre with ⟨b, hb, hbSub⟩
  obtain ⟨q, hsq, hqb⟩ := exists_rat_btwn (show (s : ℝ) < b by exact_mod_cast hb.1)
  have hq_nonneg : 0 ≤ q := by
    have hq_pos : (0 : ℝ) < q := by
      have hs_nonneg : (0 : ℝ) ≤ s := by
        exact_mod_cast (show (0 : NNReal) ≤ s by positivity)
      linarith
    have hq_pos_rat : (0 : ℚ) < q := by
      exact_mod_cast hq_pos
    exact le_of_lt hq_pos_rat
  let qnn : ℚ≥0 := ⟨q, hq_nonneg⟩
  refine ⟨qnn, ?_, ?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < q by linarith)
  · exact lt_of_lt_of_le (by exact_mod_cast hqb) hb.2
  · exact hbSub ⟨by exact_mod_cast (le_of_lt hsq), by exact_mod_cast hqb⟩

/-- Helper for Exercise 21.4.4: for a fixed later horizon `u > t`, the event `{τ_[X,U] ≤ t}` is
the countable intersection of rational-hit events strictly before each rational `r ∈ (t, u)`. -/
private theorem strictPositiveHittingTime_le_open_event_eq_iInter_iUnion
    {X : NNReal → Ω → E} (hXrc : HasRightContinuousPaths X) {U : Set E} (hU : IsOpen U)
    {t u : NNReal} (htu : t < u) :
    {ω | strictPositiveHittingTime X U ω ≤ t} =
      ⋂ r : {r : ℚ≥0 // t < (r : NNReal) ∧ (r : NNReal) < u},
        ⋃ q : {q : ℚ≥0 // 0 < q ∧ (q : NNReal) < (r : NNReal)},
          {ω | X q ω ∈ U} := by
  ext ω
  constructor
  · intro hτ
    refine Set.mem_iInter.2 fun r ↦ ?_
    have hε : 0 < (r : NNReal) - t := tsub_pos_iff_lt.mpr r.2.1
    obtain ⟨s, hs0, hsU, hs_lt⟩ :=
      (strictPositiveHittingTime_le_iff_forall_exists_lt (X := X) (A := U) (ω := ω)
        (t := t)).1 hτ ((r : NNReal) - t) hε
    have hsr : s < (r : NNReal) := by
      calc
        s < t + ((r : NNReal) - t) := hs_lt
        _ = (r : NNReal) := by rw [add_tsub_cancel_of_le r.2.1.le]
    rcases exists_nnrat_hit_lt_of_open_of_rightContinuous hXrc hU hs0 hsr hsU with
      ⟨q, hq0, hqr, hqU⟩
    exact Set.mem_iUnion.2 ⟨⟨q, hq0, hqr⟩, hqU⟩
  · intro hApprox
    refine (strictPositiveHittingTime_le_iff_forall_exists_lt (X := X) (A := U) (ω := ω)
      (t := t)).2 ?_
    intro ε hε
    obtain ⟨r, htr, hru⟩ :=
      exists_rat_btwn (show (t : ℝ) < min u (t + ε) by
        exact_mod_cast lt_min htu (lt_add_of_pos_right t hε))
    have hr_nonneg : 0 ≤ r := by
      have hr_pos : (0 : ℝ) < r := by
        have ht_nonneg : (0 : ℝ) ≤ t := by
          exact_mod_cast (show (0 : NNReal) ≤ t by positivity)
        linarith
      have hr_pos_rat : (0 : ℚ) < r := by
        exact_mod_cast hr_pos
      exact le_of_lt hr_pos_rat
    let qrat : ℚ≥0 := ⟨r, hr_nonneg⟩
    have hqrat_left : t < (qrat : NNReal) := by
      exact_mod_cast htr
    have hqrat_right : (qrat : NNReal) < u := by
      exact lt_of_lt_of_le (by exact_mod_cast hru) (min_le_left _ _)
    let rSub : {r : ℚ≥0 // t < (r : NNReal) ∧ (r : NNReal) < u} :=
      ⟨qrat, hqrat_left, hqrat_right⟩
    rcases Set.mem_iUnion.1 (Set.mem_iInter.1 hApprox rSub) with ⟨q, hqU⟩
    have hq0 : (0 : NNReal) < q := by
      exact_mod_cast q.2.1
    refine ⟨q, hq0, hqU, ?_⟩
    exact lt_trans q.2.2 (lt_of_lt_of_le hru (min_le_right _ _))

end Topological

section Measurable

variable [MeasurableSpace Ω] [TopologicalSpace E] [MeasurableSpace E] [BorelSpace E]

/-- Helper for Exercise 21.4.4: for an open target set `U`, the strict positive hitting time
`τ_[X, U]` is a stopping time for the right-continuous natural filtration generated by a
right-continuous path. -/
theorem strictPositiveHittingTime_isStoppingTime_rightCont_of_open
    {X : NNReal → Ω → E} [PolishSpace E] (hXsm : ∀ t, StronglyMeasurable (X t))
    (hXrc : HasRightContinuousPaths X) {U : Set E} (hU : IsOpen U) :
    IsStoppingTime (Filtration.rightCont (Filtration.natural X hXsm)) (τ_[X, U]) := by
  let ℱX : Filtration NNReal inferInstance := Filtration.natural X hXsm
  have hStrong : StronglyAdapted ℱX X := Filtration.stronglyAdapted_natural hXsm
  intro t
  change MeasurableSet[(Filtration.rightCont ℱX) t] {ω | strictPositiveHittingTime X U ω ≤ t}
  rw [Filtration.rightCont_eq (𝓕 := ℱX) t]
  have hMeas :
      ∀ u > t, MeasurableSet[ℱX u] {ω | strictPositiveHittingTime X U ω ≤ t} := by
    intro u htu
    rw [strictPositiveHittingTime_le_open_event_eq_iInter_iUnion hXrc hU htu]
    refine MeasurableSet.iInter fun r ↦ MeasurableSet.iUnion fun q ↦ ?_
    have hq_le_u : (q : NNReal) ≤ u := (lt_trans q.2.2 r.2.2).le
    have hmeas : StronglyMeasurable[ℱX u] (fun ω ↦ X (q : NNReal) ω) := by
      exact hStrong.stronglyMeasurable_le (i := (q : NNReal)) (j := u) hq_le_u
    exact hmeas.measurable hU.measurableSet
  simpa [MeasurableSpace.measurableSet_iInf] using hMeas

/-- Exercise 21.4.4: the repaired owner theorem records the measurable stopping event coming from
the right-continuous open-target result for the strict positive hitting time. -/
theorem measurableSet_lt_strictPositiveHittingTime_closed
    {X : NNReal → Ω → E} [PolishSpace E] (hXsm : ∀ t, StronglyMeasurable (X t))
    (hXrc : HasRightContinuousPaths X) {U : Set E} (hU : IsOpen U) (t : NNReal) :
    MeasurableSet[(Filtration.rightCont (Filtration.natural X hXsm)) t]
      {ω | strictPositiveHittingTime X U ω ≤ t} := by
  -- Proof comment: read the event directly from the stopping-time characterization above.
  exact
    (strictPositiveHittingTime_isStoppingTime_rightCont_of_open
      (X := X) hXsm hXrc hU) t

end Measurable

end ProbabilityTheory
