module

public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_4_definition_2_23.MinimumCut

public section

namespace SimpleGraph

universe u

variable {V : Type u}

section MinimumCut

variable (G : SimpleGraph V) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]

/-- Helper for Algorithm 2.2: the selected cut is no heavier than any proper cut side. -/
private lemma selectedCutWeight_le_of_isProperCutSide
    (w : G.edgeSet → ℝ)
    (s : V)
    (F : ∀ _ : {t : V // t ≠ s}, Finset V)
    (hFmin :
      ∀ t : {t : V // t ≠ s},
        ∀ T : Finset V,
          SimpleGraph.IsSTCutSide s (t : V) T →
            G.cutWeight w (F t) ≤ G.cutWeight w T)
    (tStar : {t : V // t ≠ s})
    (htStar : ∀ t : {t : V // t ≠ s}, G.cutWeight w (F tStar) ≤ G.cutWeight w (F t))
    (T : Finset V)
    (hT : SimpleGraph.IsProperCutSide T) :
    G.cutWeight w (F tStar) ≤ G.cutWeight w T := by
  rw [SimpleGraph.isProperCutSide_iff] at hT
  by_cases hsT : s ∈ T
  · -- Use a vertex outside `T` to compare `T` with one of the enumerated minimum `s,t`-cuts.
    have hExistsOutside : ∃ t : V, t ∉ T := by
      classical
      have hNotAll : ¬ ∀ t : V, t ∈ T := by
        simpa [Finset.eq_univ_iff_forall] using hT.2
      exact Classical.not_forall.mp hNotAll
    obtain ⟨t, ht_notin⟩ := hExistsOutside
    have ht_ne_s : t ≠ s := by
      intro hEq
      apply ht_notin
      simpa [hEq] using hsT
    let tSub : {t : V // t ≠ s} := ⟨t, ht_ne_s⟩
    have hTcut : SimpleGraph.IsSTCutSide s (tSub : V) T := by
      -- In this branch, `T` itself separates `s` from the chosen outside vertex.
      rw [SimpleGraph.isSTCutSide_iff]
      exact ⟨hsT, ht_notin⟩
    calc
      G.cutWeight w (F tStar) ≤ G.cutWeight w (F tSub) := htStar tSub
      _ ≤ G.cutWeight w T := hFmin tSub T hTcut
  · -- If `s ∉ T`, pass to the complementary side, which does contain `s`.
    obtain ⟨t, ht_in⟩ := hT.1
    have ht_ne_s : t ≠ s := by
      intro hEq
      apply hsT
      simpa [hEq] using ht_in
    let tSub : {t : V // t ≠ s} := ⟨t, ht_ne_s⟩
    have hCompCut :
        SimpleGraph.IsSTCutSide s (tSub : V) (SimpleGraph.cutComplement T) := by
      -- The complementary side contains `s` and omits the chosen vertex from `T`.
      rw [SimpleGraph.isSTCutSide_iff]
      refine ⟨?_, ?_⟩
      · rw [SimpleGraph.cutComplement_eq_sdiff]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ s, hsT⟩
      · rw [SimpleGraph.cutComplement_eq_sdiff]
        intro htComp
        exact (Finset.mem_sdiff.mp htComp).2 ht_in
    calc
      G.cutWeight w (F tStar) ≤ G.cutWeight w (F tSub) := htStar tSub
      _ ≤ G.cutWeight w (SimpleGraph.cutComplement T) := hFmin tSub _ hCompCut
      _ = G.cutWeight w T := SimpleGraph.cutWeight_compl G w T

/-- Algorithm 2.2. In the textbook setting of a connected undirected graph with nonnegative edge
weights, if `F t` is a minimum-weight `s,t`-cut side for every `t ≠ s` and `tStar` minimizes the
cut weight among these choices, then the returned cut `F tStar` has minimum total weight among all
proper cuts. The formal conclusion only depends on the displayed cut minimality hypotheses. The
companion theorem `repeatedSTCuts_isLeast_cutObjectiveValue` records the same conclusion on the
canonical owner `SimpleGraph.MinimumCut.cutObjectiveValues`. The textbook cut is represented here
by the side containing `s`. -/
theorem repeatedSTCuts_returns_minimumProperCut
    (w : G.edgeSet → ℝ)
    (s : V)
    (F : ∀ _ : {t : V // t ≠ s}, Finset V)
    (hFcut : ∀ t : {t : V // t ≠ s}, SimpleGraph.IsSTCutSide s (t : V) (F t))
    (hFmin :
      ∀ t : {t : V // t ≠ s},
        ∀ T : Finset V,
          SimpleGraph.IsSTCutSide s (t : V) T →
            G.cutWeight w (F t) ≤ G.cutWeight w T)
    (tStar : {t : V // t ≠ s})
    (htStar : ∀ t : {t : V // t ≠ s}, G.cutWeight w (F tStar) ≤ G.cutWeight w (F t)) :
    SimpleGraph.IsProperCutSide (F tStar) ∧
      ∀ T : Finset V,
        SimpleGraph.IsProperCutSide T → G.cutWeight w (F tStar) ≤ G.cutWeight w T := by
  refine ⟨(hFcut tStar).isProperCutSide, ?_⟩
  intro T hT
  exact selectedCutWeight_le_of_isProperCutSide G w s F hFmin tStar htStar T hT

/-- Companion to `repeatedSTCuts_returns_minimumProperCut`: the returned cut weight is least in the
canonical owner `SimpleGraph.MinimumCut.cutObjectiveValues`. -/
theorem repeatedSTCuts_isLeast_cutObjectiveValue
    (w : G.edgeSet → ℝ)
    (s : V)
    (F : ∀ _ : {t : V // t ≠ s}, Finset V)
    (hFcut : ∀ t : {t : V // t ≠ s}, SimpleGraph.IsSTCutSide s (t : V) (F t))
    (hFmin :
      ∀ t : {t : V // t ≠ s},
        ∀ T : Finset V,
          SimpleGraph.IsSTCutSide s (t : V) T →
            G.cutWeight w (F t) ≤ G.cutWeight w T)
    (tStar : {t : V // t ≠ s})
    (htStar : ∀ t : {t : V // t ≠ s}, G.cutWeight w (F tStar) ≤ G.cutWeight w (F t)) :
    IsLeast (SimpleGraph.MinimumCut.cutObjectiveValues G w) (G.cutWeight w (F tStar)) := by
  refine ⟨?_, ?_⟩
  · exact SimpleGraph.MinimumCut.cutWeight_mem_cutObjectiveValues G w
      (hFcut tStar).isProperCutSide
  · intro r hr
    rcases (SimpleGraph.MinimumCut.mem_cutObjectiveValues_iff G).1 hr with
      ⟨T, hT, rfl⟩
    exact (repeatedSTCuts_returns_minimumProperCut G w s F hFcut hFmin tStar htStar).2 T hT

end MinimumCut

end SimpleGraph

end
