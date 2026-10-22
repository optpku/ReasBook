/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_4
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Definition_1_31
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Text_1_0_56_1_36

-- Declarations for this item will be appended below by the statement pipeline.

open Set

universe u

namespace ERealFunction

variable {X : Type u}

/-- Helper for Lemma 1.32: the textbook real-height epigraph is the pullback of the canonical
`EReal` epigraph along the coercion of the second coordinate. -/
private lemma epigraph_eq_preimage_ereal_epigraph (f : X → EReal) :
    epigraph f =
      (fun p : X × ℝ ↦ (p.1, (p.2 : EReal))) ⁻¹' {q : X × EReal | f q.1 ≤ q.2} := by
  rfl

variable [TopologicalSpace X]

/-- Helper for Lemma 1.32: monotonicity of the pointwise liminf under pointwise order. -/
private lemma liminfAt_mono {f g : X → EReal} (hfg : f ≤ g) (x : X) :
    liminfAt f x ≤ liminfAt g x := by
  -- The filter liminf is monotone under eventual pointwise order.
  exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hfg)

/-- Helper for Lemma 1.32: the constant-on-open-set function with value `ξ` and value `⊥`
outside is lower semicontinuous. -/
private lemma lowerSemicontinuous_piecewise_bot
    {U : Set X} [DecidablePred (· ∈ U)] (hU : IsOpen U)
    (ξ : EReal) :
    LowerSemicontinuous (fun x : X ↦ if x ∈ U then ξ else ⊥) := by
  -- At points of `U`, openness keeps the value equal to `ξ`; outside `U`, the claim is vacuous.
  rw [lowerSemicontinuous_iff]
  intro x
  rw [lowerSemicontinuousAt_iff]
  by_cases hx : x ∈ U
  · intro y hy
    have hyξ : y < ξ := by
      simpa [hx] using hy
    filter_upwards [hU.mem_nhds hx] with z hz
    simpa [hz] using hyξ
  · intro y hy
    simp [hx] at hy

-- Proof sketch: rewrite the lower semicontinuous envelope as the pointwise `iSup` of the subtype
-- of lower semicontinuous minorants; `lowerSemicontinuous_iSup` gives lower semicontinuity, and
-- the subtype indexing enforces the minorant and maximality properties.
/-- Lemma 1.32: the lower semicontinuous envelope is the greatest lower semicontinuous minorant of
`f`. -/
theorem lowerSemicontinuousHull_isGreatest (f : X → EReal) :
    IsGreatest {g : X → EReal | LowerSemicontinuous g ∧ g ≤ f}
      (lowerSemicontinuousEnvelope f) := by
  have hEnvelope_eq_iSup :
      lowerSemicontinuousEnvelope f =
        fun x ↦ ⨆ g : {g : X → EReal // g ∈ lowerSemicontinuousMinorants f}, g.1 x := by
    funext x
    rw [lowerSemicontinuousEnvelope_apply]
    apply le_antisymm
    · refine sSup_le fun y hy ↦ ?_
      rcases hy with ⟨g, hg, rfl⟩
      exact le_iSup_of_le ⟨g, hg⟩ le_rfl
    · refine iSup_le fun g ↦ ?_
      exact le_sSup ⟨g.1, g.2, rfl⟩
  -- The hull belongs to the class of lower semicontinuous minorants.
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · -- Lower semicontinuity follows from lower semicontinuity of each indexed minorant.
      simpa [hEnvelope_eq_iSup, lowerSemicontinuousMinorants] using
        (lowerSemicontinuous_iSup
          fun g : {g : X → EReal // g ∈ lowerSemicontinuousMinorants f} ↦ g.2.1)
    · -- Every indexed function is a minorant of `f`, so their supremum is as well.
      intro x
      rw [hEnvelope_eq_iSup]
      exact iSup_le fun g ↦ g.2.2 x
  · intro g hg x
    -- Any lower semicontinuous minorant appears in the indexing subtype.
    rw [hEnvelope_eq_iSup]
    exact le_iSup_of_le ⟨g, hg⟩ le_rfl

-- Proof sketch: the main envelope theorem gives that `lowerSemicontinuousEnvelope f` is lower
-- semicontinuous; then apply the epigraph characterization of lower semicontinuity.
/-- The epigraph of the lower semicontinuous envelope is closed. -/
theorem isClosed_epi_lowerSemicontinuousHull (f : X → EReal) :
    IsClosed (epigraph (lowerSemicontinuousEnvelope f)) := by
  rw [epigraph_eq_preimage_ereal_epigraph]
  exact (LowerSemicontinuous.isClosed_epigraph
      (lowerSemicontinuousHull_isGreatest f).1.1).preimage
    (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

-- Proof sketch: any point with `f x < +∞` also satisfies `lowerSemicontinuousEnvelope f x < +∞`
-- because the envelope is majorized by `f`.
/-- The domain of `f` is contained in the domain of its lower semicontinuous hull. -/
theorem dom_subset_dom_lowerSemicontinuousHull (f : X → EReal) :
    dom f ⊆ dom (lowerSemicontinuousEnvelope f) := by
  intro x hx
  -- The hull is pointwise majorized by `f`, so finiteness of `f x` propagates to the hull.
  exact lt_of_le_of_lt ((lowerSemicontinuousHull_isGreatest f).1.2 x) hx

/-- Helper for Lemma 1.32: restricting a lower semicontinuous function to a closed set and
sending the complement to `+∞` preserves lower semicontinuity. -/
private lemma lowerSemicontinuous_piecewise_top_of_isClosed
    {s : Set X} [DecidablePred (· ∈ s)] {g : X → EReal} (hs : IsClosed s)
    (hg : LowerSemicontinuous g) :
    LowerSemicontinuous (fun x : X ↦ if x ∈ s then g x else ⊤) := by
  -- At points of `s`, lower semicontinuity comes from `g`; away from `s`, the open complement
  -- forces the value to stay equal to `⊤` on a neighborhood.
  rw [lowerSemicontinuous_iff]
  intro x
  rw [lowerSemicontinuousAt_iff]
  by_cases hx : x ∈ s
  · have hgx : LowerSemicontinuousAt g x := (lowerSemicontinuous_iff.mp hg) x
    rw [lowerSemicontinuousAt_iff] at hgx
    intro y hy
    have hyg : y < g x := by
      simpa [hx] using hy
    have hy_top : y < (⊤ : EReal) := hyg.trans_le le_top
    have h_event : ∀ᶠ z in nhds x, y < g z := hgx y hyg
    refine h_event.mp ?_
    filter_upwards with z hz_g
    by_cases hz_mem : z ∈ s
    · simpa [hz_mem] using hz_g
    · simpa [hz_mem] using hy_top
  · intro y hy
    have hy_top : y < (⊤ : EReal) := by
      simpa [hx] using hy
    refine Filter.mem_of_superset (hs.isOpen_compl.mem_nhds hx) ?_
    intro z hz
    have hz' : z ∉ s := by
      simpa using hz
    simpa [hz'] using hy_top

/-- Helper for Lemma 1.32: away from the closure of the domain, the lower semicontinuous hull takes
the value `+∞`. -/
private lemma lowerSemicontinuousHull_eq_top_of_notMem_closure_dom (f : X → EReal)
    {x : X} (hx : x ∉ closure (dom f)) :
    lowerSemicontinuousEnvelope f x = ⊤ := by
  classical
  let g : X → EReal :=
    fun y ↦ if y ∈ closure (dom f) then lowerSemicontinuousEnvelope f y else ⊤
  have hg_lsc : LowerSemicontinuous g := by
    -- The closed-set truncation of the hull is still lower semicontinuous.
    simpa [g] using
      (lowerSemicontinuous_piecewise_top_of_isClosed isClosed_closure
        (lowerSemicontinuousHull_isGreatest f).1.1)
  have hg_le_f : g ≤ f := by
    -- On the closure we use the hull minorization; outside it, `f` must already equal `⊤`.
    intro y
    by_cases hy : y ∈ closure (dom f)
    · simpa [g, hy] using (lowerSemicontinuousHull_isGreatest f).1.2 y
    · have hy_not_dom : y ∉ dom f := fun hy_dom ↦ hy (subset_closure hy_dom)
      have htop_le : (⊤ : EReal) ≤ f y := le_of_not_gt hy_not_dom
      simpa [g, hy] using htop_le
  have hg_le_hull : g ≤ lowerSemicontinuousEnvelope f :=
    (lowerSemicontinuousHull_isGreatest f).2 ⟨hg_lsc, hg_le_f⟩
  -- Evaluating the comparison at a point outside the closure forces the hull to be `⊤` there.
  have htop_le : (⊤ : EReal) ≤ lowerSemicontinuousEnvelope f x := by
    simpa [g, hx] using hg_le_hull x
  exact le_antisymm le_top htop_le

-- Proof sketch: truncate the hull outside `closure (dom f)` by setting it equal to
-- `+∞`; the resulting function is still lower semicontinuous and majorized by `f`, so maximality
-- of the hull forces the hull to be `+∞` away from `closure (dom f)`.
/-- The domain of the lower semicontinuous hull is contained in the closure of the domain of `f`. -/
theorem dom_lowerSemicontinuousHull_subset_closure_dom (f : X → EReal) :
    dom (lowerSemicontinuousEnvelope f) ⊆ closure (dom f) := by
  intro x hx
  -- Route correction: the domain inclusion is proved by the closed-set truncation/maximality
  -- argument, not by forward-referencing the later liminf formula.
  by_contra hx_closure
  have htop : lowerSemicontinuousEnvelope f x = ⊤ :=
    lowerSemicontinuousHull_eq_top_of_notMem_closure_dom f hx_closure
  have hx_not_dom : ¬ x ∈ dom (lowerSemicontinuousEnvelope f) := by
    simp [mem_dom_iff, htop]
  exact hx_not_dom hx

-- Proof sketch: show first that `x ↦ liminfAt f x` is lower semicontinuous and majorized by `f`,
-- hence bounded above by the hull; then compare any lower semicontinuous minorant of `f` with the
-- neighborhood-infimum formula for `liminfAt`.
/-- The lower semicontinuous hull agrees pointwise with the lower limit inferior of `f`. -/
theorem lowerSemicontinuousHull_eq_liminfAt (f : X → EReal) (x : X) :
    lowerSemicontinuousEnvelope f x = liminfAt f x := by
  classical
  refine le_antisymm ?_ ?_
  · -- Lower semicontinuity of the hull gives the upper bound by the liminf.
    exact ((lowerSemicontinuousHull_isGreatest f).1.1.le_liminf x).trans
      (liminfAt_mono (lowerSemicontinuousHull_isGreatest f).1.2 x)
  · -- Any real level strictly below the liminf can be realized by an open lower semicontinuous
    -- minorant, forcing the hull to stay above it.
    refine (EReal.ge_of_forall_gt_iff_ge).1 ?_
    intro z hz
    have hz_event :
        {y : X | (z : EReal) < f y} ∈ nhds x := by
      simpa [liminfAt] using
        (Filter.eventually_lt_of_lt_liminf hz : ∀ᶠ y in nhds x, (z : EReal) < f y)
    rcases mem_nhds_iff.mp hz_event with ⟨U, hUsub, hUopen, hxU⟩
    let g : X → EReal := fun y ↦ if y ∈ U then (z : EReal) else ⊥
    have hg_lsc : LowerSemicontinuous g := by
      -- The open set `U` supports a constant value, while outside `U` the value is `⊥`.
      simpa [g] using (lowerSemicontinuous_piecewise_bot hUopen (z : EReal))
    have hg_le_f : g ≤ f := by
      -- On `U` we use the neighborhood lower bound, and outside `U` we use `⊥ ≤ f`.
      intro y
      by_cases hy : y ∈ U
      · simpa [g, hy] using (hUsub hy).le
      · simp [g, hy]
    have hg_le_hull : g ≤ lowerSemicontinuousEnvelope f :=
      (lowerSemicontinuousHull_isGreatest f).2 ⟨hg_lsc, hg_le_f⟩
    -- Evaluating the auxiliary minorant at `x` gives the desired lower bound.
    simpa [g, hxU] using hg_le_hull x

-- Proof sketch: use the pointwise formula for the hull as a limit inferior, together with the
-- neighborhood characterization of lower semicontinuity at a point.
/-- A function is lower semicontinuous at `x` exactly when its lower semicontinuous hull agrees
with it at `x`. -/
theorem lowerSemicontinuousAt_iff_lowerSemicontinuousHull_eq (f : X → EReal) (x : X) :
    LowerSemicontinuousAt f x ↔ lowerSemicontinuousEnvelope f x = f x := by
  constructor
  · intro hfx
    -- The hull is always below `f`, while lower semicontinuity gives the reverse inequality.
    apply le_antisymm
    · exact (lowerSemicontinuousHull_isGreatest f).1.2 x
    · calc
        f x ≤ liminfAt f x := by
          simpa [liminfAt] using
            (LowerSemicontinuousAt.le_liminf hfx : f x ≤ Filter.liminf f (nhds x))
        _ = lowerSemicontinuousEnvelope f x := by
          symm
          exact lowerSemicontinuousHull_eq_liminfAt f x
  · intro hEq
    -- Rewriting the hull as the liminf turns the assumed equality into the standard criterion.
    rw [lowerSemicontinuousAt_iff_le_liminf]
    calc
      f x = lowerSemicontinuousEnvelope f x := hEq.symm
      _ = liminfAt f x := lowerSemicontinuousHull_eq_liminfAt f x
      _ ≤ Filter.liminf f (nhds x) := by
        rfl

/-- Helper for Lemma 1.32: each real-height epigraph point of the lower semicontinuous hull lies
in the closure of the real-height epigraph of the original function. -/
private lemma mem_closure_epigraph_of_mem_epigraph_lowerSemicontinuousHull
    (f : X → EReal) {x : X} {ξ : ℝ}
    (hξ : lowerSemicontinuousEnvelope f x ≤ (ξ : EReal)) :
    (x, ξ) ∈ closure (epigraph f) := by
  -- Test an arbitrary neighborhood of `(x, ξ)` and find an epigraph point of `f` inside it by
  -- combining a product neighborhood with a strict `liminf` witness below a nearby real height.
  rw [mem_closure_iff_nhds]
  intro t ht
  rcases mem_nhds_prod_iff.mp ht with ⟨V, hV, W, hW, hVW⟩
  obtain ⟨v, hξv, hvW⟩ := exists_Ico_subset_of_mem_nhds hW ⟨ξ + 1, by linarith⟩
  let u : ℝ := (ξ + v) / 2
  have hξu : ξ < u := by
    dsimp [u]
    linarith
  have huv : u < v := by
    dsimp [u]
    linarith
  have huW : u ∈ W := by
    apply hvW
    exact ⟨le_of_lt hξu, huv⟩
  have hHull_lt : lowerSemicontinuousEnvelope f x < (u : EReal) := by
    exact lt_of_le_of_lt hξ (by exact_mod_cast hξu)
  have hliminf_lt : liminfAt f x < (u : EReal) := by
    simpa [lowerSemicontinuousHull_eq_liminfAt f x] using hHull_lt
  have hbounded : (nhds x).IsCoboundedUnder (· ≥ ·) f := by
    isBoundedDefault
  have hfreq : ∃ᶠ y in nhds x, f y < (u : EReal) := by
    exact (Filter.frequently_lt_of_liminf_lt hbounded hliminf_lt :
      ∃ᶠ y in nhds x, f y < (u : EReal))
  have hfreqV : ∃ᶠ y in nhds x, f y < (u : EReal) ∧ y ∈ V := by
    exact hfreq.and_eventually hV
  obtain ⟨y, hy_lt, hyV⟩ := hfreqV.exists
  refine ⟨(y, u), ?_⟩
  constructor
  · exact hVW ⟨hyV, huW⟩
  · -- The chosen point lies below the nearby height `u`, hence it belongs to `epigraph f`.
    simpa [epigraph] using le_of_lt hy_lt

-- Proof sketch: one inclusion follows because `epi f ⊆ epi (lowerSemicontinuousHull f)` and the
-- hull epigraph is closed; for the reverse inclusion, use the pointwise `liminf` formula to hit
-- every neighborhood of a point of `epi (lowerSemicontinuousHull f)` with a point of `epi f`.
/-- The epigraph of the lower semicontinuous hull is the closure of the epigraph of `f`. -/
theorem epi_lowerSemicontinuousHull_eq_closure_epi (f : X → EReal) :
    epigraph (lowerSemicontinuousEnvelope f) = closure (epigraph f) := by
  ext p
  constructor
  · rcases p with ⟨x, ξ⟩
    intro hp
    -- The hard inclusion is exactly the closure helper for points of the hull epigraph.
    exact mem_closure_epigraph_of_mem_epigraph_lowerSemicontinuousHull f hp
  · intro hp
    -- The easy inclusion comes from `epigraph f ⊆ epigraph (lowerSemicontinuousHull f)` and
    -- closedness.
    exact closure_minimal
      (fun (q : X × ℝ) hq ↦ le_trans ((lowerSemicontinuousHull_isGreatest f).1.2 q.1) hq)
      (isClosed_epi_lowerSemicontinuousHull f) hp

end ERealFunction
