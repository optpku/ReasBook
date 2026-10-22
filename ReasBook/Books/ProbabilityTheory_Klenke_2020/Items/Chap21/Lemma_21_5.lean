/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap17.Definition_17_12
import Books.ProbabilityTheory_Klenke_2020.Items.Chap21.Definition_21_1

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set

noncomputable section

universe u v

namespace ProbabilityTheory

variable {Ω : Type u} [MeasurableSpace Ω]
variable {E : Type v} [TopologicalSpace E]

/-- Helper for Lemma 21.5: the countable dense-right subset of an interval `I ⊆ ℝ` given by the
rational times together with a possible maximal endpoint. -/
private def rationalOrTopIndices (I : Set ℝ) : Set I :=
  {t | ∃ q : ℚ, (t : ℝ) = q} ∪ {t | IsTop t}

variable {I : Set ℝ}

/-- Helper for Lemma 21.5: the rational-or-top index set inside an interval subtype is countable. -/
private lemma countableRationalOrTopIndices :
    (rationalOrTopIndices I).Countable := by
  -- Rational times are the pullback of the countable set `Set.range Rat.cast`.
  have hRat :
      ({t : I | ∃ q : ℚ, (t : ℝ) = q} : Set I).Countable := by
    have hRange : (Set.range (Rat.cast : ℚ → ℝ)).Countable := Set.countable_range _
    -- Pull the countable ambient rational set back along the subtype coercion.
    have hPre : ((fun t : I ↦ (t : ℝ)) ⁻¹' Set.range (Rat.cast : ℚ → ℝ)).Countable := by
      refine hRange.preimage ?_
      intro a b hab
      exact Subtype.ext hab
    -- Normalize the pullback set to the existential description used in `rationalOrTopIndices`.
    convert hPre using 1
    ext t
    simp [Set.mem_range, eq_comm]
  -- A top element is unique when it exists, so the top part is countable as well.
  have hTop : ({t : I | IsTop t} : Set I).Countable := Set.countable_isTop I
  simpa [rationalOrTopIndices] using hRat.union hTop

/-- Helper for Lemma 21.5: a maximal endpoint of the interval subtype belongs to the
distinguished rational-or-top index set. -/
private lemma memRationalOrTopIndices_of_isTop {t : I} (ht : IsTop t) :
    t ∈ rationalOrTopIndices I := by
  exact Or.inr ht

/-- Helper for Lemma 21.5: every time `t : I` lies in the closure of the rational-or-top times to
its right. -/
private lemma memClosure_rationalOrTopIndices_Ici
    (hI : I.OrdConnected) (t : I) :
    t ∈ closure (Set.Ici t ∩ rationalOrTopIndices I) := by
  classical
  by_cases ht : IsTop t
  · -- A maximal endpoint already belongs to the distinguished index set.
    exact subset_closure ⟨Set.mem_Ici.2 le_rfl, memRationalOrTopIndices_of_isTop ht⟩
  · -- Otherwise the upper slice is nontrivial, and rational points are dense in it.
    have hz : ∃ z : I, ¬ z ≤ t := by
      by_contra hNo
      apply ht
      intro z
      by_contra hzt
      exact hNo ⟨z, hzt⟩
    rcases hz with ⟨z, hz⟩
    have htz : t < z := lt_of_not_ge hz
    let s : Set ℝ := (I : Set ℝ) ∩ Set.Ici (t : ℝ)
    have hsConn : s.OrdConnected := hI.inter Set.ordConnected_Ici
    have hsNontrivial : s.Nontrivial := by
      refine ⟨(t : ℝ), ⟨t.2, Set.mem_Ici.2 le_rfl⟩, (z : ℝ), ⟨z.2, htz.le⟩, ne_of_lt htz⟩
    have htClosureRat : (t : ℝ) ∈ closure (s ∩ Set.range (Rat.cast : ℚ → ℝ)) := by
      rw [closure_ordConnected_inter_rat hsConn hsNontrivial]
      exact subset_closure ⟨t.2, Set.mem_Ici.2 le_rfl⟩
    have hsubset :
        s ∩ Set.range (Rat.cast : ℚ → ℝ) ⊆
          ((↑) : I → ℝ) '' (Set.Ici t ∩ rationalOrTopIndices I) := by
      intro x hx
      rcases hx with ⟨⟨hxI, hxt⟩, hxRat⟩
      rcases hxRat with ⟨q, rfl⟩
      refine ⟨⟨(q : ℝ), hxI⟩, ⟨hxt, Or.inl ⟨q, rfl⟩⟩, rfl⟩
    have htClosure :
        (t : ℝ) ∈ closure (((↑) : I → ℝ) '' (Set.Ici t ∩ rationalOrTopIndices I)) :=
      closure_mono hsubset htClosureRat
    simpa using
      (closure_subtype (x := t) (s := Set.Ici t ∩ rationalOrTopIndices I)).2 htClosure

/-- Helper for Lemma 21.5: right-continuous functions that agree on a dense-right subset agree at
the endpoint. -/
private lemma eqAt_of_eqOnDenseRight_of_continuousWithinAt
    [T2Space E] {f g : I → E} {S : Set I} {t : I}
    (ht : t ∈ closure (Set.Ici t ∩ S))
    (hf : ContinuousWithinAt f (Set.Ici t) t)
    (hg : ContinuousWithinAt g (Set.Ici t) t)
    (hEq : Set.EqOn f g (Set.Ici t ∩ S)) :
    f t = g t := by
  -- Route correction: use uniqueness of limits along `𝓝[Set.Ici t ∩ S] t` rather than the
  -- global `Set.EqOn.of_subset_closure` lemma, which needs continuity on an entire closure set.
  have hne : (nhdsWithin t (Set.Ici t ∩ S)).NeBot := mem_closure_iff_clusterPt.mp ht
  have hf' : ContinuousWithinAt f (Set.Ici t ∩ S) t := hf.mono inter_subset_left
  have hg' : ContinuousWithinAt g (Set.Ici t ∩ S) t := hg.mono inter_subset_left
  have hEq' : f =ᶠ[nhdsWithin t (Set.Ici t ∩ S)] g := hEq.eventuallyEq_of_mem self_mem_nhdsWithin
  let _ : Filter.NeBot (nhdsWithin t (Set.Ici t ∩ S)) := hne
  exact tendsto_nhds_unique_of_eventuallyEq hf' hg' hEq'

-- Proof sketch: take the union of the null disagreement events over the countable index set.
omit [TopologicalSpace E] in
/-- Countable-index case of Lemma 21.5: if two processes indexed by a countable type are
modifications of one another, then they are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_countable
    {I : Type*} (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) [Countable I] :
    AreIndistinguishable μ X Y := by
  classical
  let N₀ : Set Ω := ⋃ t : I, {ω | X t ω ≠ Y t ω}
  -- Each single-time disagreement event is null, so the countable union is null.
  have hN₀_zero : μ N₀ = 0 := by
    refine measure_iUnion_null ?_
    intro t
    simpa [Filter.EventuallyEq, ae_iff] using hXY t
  -- Replace the raw union by a measurable null superset to match `AreIndistinguishable`.
  rcases exists_measurable_superset_of_null hN₀_zero with ⟨N, hN₀_subset, hN_meas, hN_zero⟩
  refine ⟨N, hN_meas, hN_zero, ?_⟩
  intro t ω hω
  exact hN₀_subset (Set.mem_iUnion.2 ⟨t, hω⟩)

omit [TopologicalSpace E] in
/-- Helper for Lemma 21.5: an indistinguishability witness on a subtype index set gives
pathwise equality on that set outside a single null set. -/
private lemma eqOn_of_areIndistinguishable_subtype
    (μ : Measure Ω) (X Y : I → Ω → E) (J : Set I)
    (hInd : AreIndistinguishable μ (fun s : J ↦ X s.1) (fun s : J ↦ Y s.1)) :
    ∃ N, MeasurableSet N ∧ μ N = 0 ∧
      ∀ ⦃ω⦄, ω ∉ N → Set.EqOn (fun t : I ↦ X t ω) (fun t : I ↦ Y t ω) J := by
  rcases hInd with ⟨N, hN_meas, hN_zero, hN_sub⟩
  refine ⟨N, hN_meas, hN_zero, ?_⟩
  intro ω hω t ht
  -- Outside the null witness, any disagreement at an index in `J` is impossible.
  by_contra hneq
  exact hω ((hN_sub ⟨t, ht⟩) hneq)

-- Proof sketch: pass to a countable dense subset of the interval `I`, obtain a common null set
-- there, and then use almost sure right continuity and uniqueness of right limits in the
-- Hausdorff codomain to extend equality from the dense subset to every time.
/-- Lemma 21.5, interval/right-continuous case: if two processes indexed by an interval `I ⊆ ℝ`
are modifications of one another and both sample paths are almost surely right continuous on `I`,
then the processes are indistinguishable. -/
theorem indistinguishable_of_forall_aeEq_of_ordConnected_of_ae_rightContinuous
    [T2Space E]
    (μ : Measure Ω) (X Y : I → Ω → E)
    (hXY : AreModifications μ X Y) (hI : I.OrdConnected)
    (hX_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t)
    (hY_rc : ∀ᵐ ω ∂μ, ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t) :
    AreIndistinguishable μ X Y := by
  classical
  let J : Set I := rationalOrTopIndices I
  have hJ_countable : J.Countable := by
    simpa [J] using (countableRationalOrTopIndices (I := I))
  let _ : Countable J := hJ_countable.to_subtype
  let Nq₀ : Set Ω := ⋃ s : J, {ω | X s.1 ω ≠ Y s.1 ω}
  have hNq₀_zero : μ Nq₀ = 0 := by
    -- Equality at each distinguished time gives a null countable union of disagreement events.
    refine measure_iUnion_null ?_
    intro s
    simpa [Filter.EventuallyEq, ae_iff] using hXY s.1
  rcases exists_measurable_superset_of_null hNq₀_zero with
    ⟨Nq, hNq_subset, hNq_meas, hNq_zero⟩
  have hrc :
      ∀ᵐ ω ∂μ,
        (∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t) ∧
          ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t := by
    -- Intersect the two almost-sure right-continuity events.
    filter_upwards [hX_rc, hY_rc] with ω hX hY
    exact ⟨hX, hY⟩
  let Brc : Set Ω := {ω |
    ¬ ((∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t) ∧
      ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t)}
  have hBrc_zero : μ Brc = 0 := by
    -- The bad continuity event is null by the almost-sure assumptions.
    simpa [Brc, ae_iff] using hrc
  rcases exists_measurable_superset_of_null hBrc_zero with
    ⟨Nrc, hBrc_subset, hNrc_meas, hNrc_zero⟩
  refine ⟨Nq ∪ Nrc, hNq_meas.union hNrc_meas, measure_union_null hNq_zero hNrc_zero, ?_⟩
  intro t ω hω
  by_cases hωq : ω ∈ Nq
  · exact Or.inl hωq
  by_cases hωrc : ω ∈ Nrc
  · exact Or.inr hωrc
  -- Outside both null sets, the sample paths are right-continuous and agree on the dense-right
  -- rational-or-top subset, hence they agree at the current time `t`.
  have hωcont :
      (∀ t : I, ContinuousWithinAt (processPath X ω) (Ici t) t) ∧
        ∀ t : I, ContinuousWithinAt (processPath Y ω) (Ici t) t := by
    by_contra hbad
    exact hωrc (hBrc_subset (by simpa [Brc] using hbad))
  have hωeqJ : Set.EqOn (fun s : I ↦ X s ω) (fun s : I ↦ Y s ω) J := by
    -- Outside `Nq`, no distinguished time can lie in the disagreement union `Nq₀`.
    intro s hs
    by_contra hneq
    exact hωq <| hNq_subset <| Set.mem_iUnion.2 ⟨⟨s, hs⟩, hneq⟩
  have htEq : X t ω = Y t ω := by
    -- Extend equality from the dense-right subset to the endpoint using right continuity.
    refine eqAt_of_eqOnDenseRight_of_continuousWithinAt
      (f := fun s : I ↦ X s ω) (g := fun s : I ↦ Y s ω) (t := t) (S := J) ?_ ?_ ?_ ?_
    · simpa [J] using memClosure_rationalOrTopIndices_Ici (I := I) hI t
    · simpa [processPath_apply] using hωcont.1 t
    · simpa [processPath_apply] using hωcont.2 t
    · intro s hs
      exact hωeqJ hs.2
  exact False.elim (hω htEq)

end ProbabilityTheory
