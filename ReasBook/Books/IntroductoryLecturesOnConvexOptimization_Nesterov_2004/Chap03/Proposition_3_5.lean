/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap02.ReciprocalEpigraphOnPositiveRay
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Definition_3_3

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped WithTopConvexAnalysis
open WithTopConvexAnalysis

/- Proposition 3.5 lives in the chapter's one-dimensional `WithTop`-valued convex-analysis
domain.

Primary domain:
- the reciprocal function on `(0, ∞)`, its `⊤`-extension to `ℝ`, its epigraph, and its effective
  domain.

Sampled owner-style declarations:
- chapter `reciprocalEpigraphOnPositiveRay` from `Chap02/ReciprocalEpigraphOnPositiveRay`;
- chapter `dom f` and `WithTopConvexAnalysis.effectiveEpigraph f` from `Definition_3_3`;
- mathlib `ConvexOn`;
- mathlib `strictConvexOn_zpow`;
- mathlib `lowerSemicontinuous_iff_isClosed_epigraph`.

Best owner abstraction:
- source-facing owner: `positiveReciprocalExtension`;
- core/canonical derived owners: `dom positiveReciprocalExtension`,
  `effectiveEpigraph positiveReciprocalExtension`, and the already established Chapter 2 set owner
  `reciprocalEpigraphOnPositiveRay`.

Primitive data:
- the extended reciprocal function `positiveReciprocalExtension`.

Derived API:
- the identification of the canonical effective epigraph with the Chapter 2 owner set
  `reciprocalEpigraphOnPositiveRay`;
- convexity on `Set.Ioi 0`;
- lower semicontinuity;
- closedness of `reciprocalEpigraphOnPositiveRay`;
- identification and openness of the canonical effective domain.

Source/core/bridge triage:
- source-facing: `positiveReciprocalExtension`;
- core/canonical: `dom`, `effectiveEpigraph`, `ConvexOn`, `LowerSemicontinuous`;
- bridge/view: the epigraph-identification theorem relating the Chapter 3 extension to the
  Chapter 2 owner set, and the source-facing named consequences about this function.

This file therefore keeps the reciprocal extension itself as the owner declaration, but reuses the
chapter owners `dom` and `effectiveEpigraph` together with the existing Chapter 2 owner
`reciprocalEpigraphOnPositiveRay` for the effective-domain and epigraph surfaces instead of
introducing parallel local set definitions or keeping closedness only on a longer bridge/view
expression. -/

/-- The reciprocal function on `(0, ∞)` extended by `⊤` on the nonpositive reals. -/
def positiveReciprocalExtension (x : ℝ) : WithTop ℝ :=
  if 0 < x then ((1 / x : ℝ) : WithTop ℝ) else ⊤

/-- Helper for Proposition 3.5: the effective domain of the reciprocal extension is exactly the
positive ray. -/
lemma positiveReciprocalExtension_mem_dom_iff (x : ℝ) :
    x ∈ dom positiveReciprocalExtension ↔ 0 < x := by
  -- The extension is finite exactly on the positive branch of the defining `if`.
  by_cases hx : 0 < x
  · simp [positiveReciprocalExtension, withTopEffectiveDomain, hx]
  · simp [positiveReciprocalExtension, withTopEffectiveDomain, hx]

/-- Helper for Proposition 3.5: the strict superlevel sets of the reciprocal extension are either
all of `ℝ` or an open left ray, depending on the threshold. -/
lemma positiveReciprocalExtension_preimage_Ioi_coe (r : ℝ) :
    positiveReciprocalExtension ⁻¹' Set.Ioi (r : WithTop ℝ) =
      if r ≤ 0 then Set.univ else Set.Iio (1 / r) := by
  by_cases hr : r ≤ 0
  · -- For nonpositive thresholds, both the finite branch and the `⊤` branch lie above `r`.
    ext x
    constructor
    · intro _
      simp [hr]
    · intro _
      by_cases hx : 0 < x
      · have hxr : r < 1 / x := lt_of_le_of_lt hr (one_div_pos.mpr hx)
        simpa [Set.mem_preimage, Set.mem_Ioi, positiveReciprocalExtension, hx, one_div] using hxr
      · simp [Set.mem_preimage, Set.mem_Ioi, positiveReciprocalExtension, hx]
  · have hr0 : 0 < r := lt_of_not_ge hr
    -- For positive thresholds, the finite branch reduces to the standard reciprocal inequality.
    ext x
    by_cases hx : 0 < x
    · have hcomparison : r < 1 / x ↔ x < 1 / r := (lt_one_div hx hr0).symm
      simpa [Set.mem_preimage, Set.mem_Ioi, positiveReciprocalExtension, hx, hr0, one_div] using
        hcomparison
    · have hx_lt : x < 1 / r := lt_of_le_of_lt (le_of_not_gt hx) (one_div_pos.mpr hr0)
      simpa [Set.mem_preimage, Set.mem_Ioi, positiveReciprocalExtension, hr, hx, one_div] using
        hx_lt

/-- The canonical effective epigraph of `positiveReciprocalExtension` is exactly the Chapter 2
owner set `reciprocalEpigraphOnPositiveRay`. -/
-- Proof sketch: expand `effectiveEpigraph`, `dom`, and `positiveReciprocalExtension`; the
-- effective-domain condition is exactly `0 < x`, and on that domain the value is `1 / x`,
-- leaving the positive-ray epigraph inequality from
-- `mem_reciprocalEpigraphOnPositiveRay_iff`.
theorem positiveReciprocalExtensionEpigraph_eq_reciprocalEpigraphOnPositiveRay :
    effectiveEpigraph positiveReciprocalExtension = reciprocalEpigraphOnPositiveRay := by
  ext p
  constructor
  · intro hp
    -- Rewrite the effective-epigraph membership into positivity plus a real inequality.
    rcases WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mp hp with ⟨hpdom, hpineq⟩
    have hp0 : 0 < p.1 := (positiveReciprocalExtension_mem_dom_iff p.1).mp hpdom
    refine mem_reciprocalEpigraphOnPositiveRay_iff p |>.2 ?_
    constructor
    · exact hp0
    · simpa [positiveReciprocalExtension, hp0, ge_iff_le] using hpineq
  · intro hp
    -- On the positive branch, the `WithTop` inequality is just the underlying real inequality.
    rcases mem_reciprocalEpigraphOnPositiveRay_iff p |>.mp hp with ⟨hp0, hpineq⟩
    refine WithTopConvexAnalysis.mem_effectiveEpigraph_iff.mpr ?_
    constructor
    · exact (positiveReciprocalExtension_mem_dom_iff p.1).mpr hp0
    · simpa [positiveReciprocalExtension, hp0, ge_iff_le] using hpineq

/- Proposition 3.5 splits naturally into the convexity of `x ↦ 1 / x` on `(0, ∞)`, the lower
semicontinuity of its `⊤`-extension, the identification of the effective domain, and the openness
of that domain. -/

/-- Proposition 3.5 (1): the reciprocal function `x ↦ 1 / x` is convex on `(0, ∞)`. -/
-- Proof sketch: apply `strictConvexOn_zpow` with exponent `(-1 : ℤ)` on `Set.Ioi 0`, then pass
-- from strict convexity to convexity.
theorem convexOn_one_div_Ioi_zero :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ ↦ 1 / x) := by
  -- The reciprocal is the `(-1)`-power on the positive ray, where mathlib already proves strict
  -- convexity.
  simpa [one_div] using
    (strictConvexOn_zpow (m := (-1 : ℤ)) (by norm_num) (by norm_num)).convexOn

/-- Proposition 3.5 (2): the reciprocal function extended by `⊤` on `(-∞, 0]` is closed,
equivalently lower semicontinuous. -/
-- Proof sketch: prove that the epigraph is closed by the sequential argument from the text, then
-- translate this to lower semicontinuity using `lowerSemicontinuous_iff_isClosed_epigraph`.
theorem lowerSemicontinuous_positiveReciprocalExtension :
    LowerSemicontinuous positiveReciprocalExtension := by
  -- The open-preimage characterization is the clean interface for this `WithTop`-valued function.
  rw [lowerSemicontinuous_iff_isOpen_preimage]
  intro y
  cases y using WithTop.recTopCoe with
  | top =>
      -- Nothing lies strictly above `⊤`.
      simp
  | coe r =>
      -- Finite thresholds reduce to the explicit superlevel description proved above.
      rw [positiveReciprocalExtension_preimage_Ioi_coe]
      by_cases hr : r ≤ 0
      · simp [hr]
      · simp [hr, isOpen_Iio]

/-- Helper for Proposition 3.5: the Chapter 2 reciprocal epigraph is sequentially closed in
`ℝ × ℝ`. -/
lemma reciprocalEpigraphOnPositiveRay_isSeqClosed :
    IsSeqClosed reciprocalEpigraphOnPositiveRay := by
  intro x p hx hp
  have hp₁ : Filter.Tendsto (fun n ↦ (x n).1) Filter.atTop (nhds p.1) :=
    (continuous_fst.tendsto p).comp hp
  have hp₂ : Filter.Tendsto (fun n ↦ (x n).2) Filter.atTop (nhds p.2) :=
    (continuous_snd.tendsto p).comp hp
  have hx_pos : ∀ n, 0 < (x n).1 := fun n ↦
    (mem_reciprocalEpigraphOnPositiveRay_iff (x n)).mp (hx n) |>.1
  have hx_ineq : ∀ n, 1 / (x n).1 ≤ (x n).2 := fun n ↦ by
    simpa [ge_iff_le] using (mem_reciprocalEpigraphOnPositiveRay_iff (x n)).mp (hx n) |>.2
  -- The convergent second coordinates are eventually bounded above, so the first coordinates are
  -- eventually bounded away from `0`.
  have hupper : ∀ᶠ n in Filter.atTop, (x n).2 < p.2 + 1 := by
    have hnhds : Set.Iio (p.2 + 1) ∈ nhds p.2 := by
      apply IsOpen.mem_nhds isOpen_Iio
      change p.2 < p.2 + 1
      linarith
    exact hp₂.eventually hnhds
  obtain ⟨n₀, hn₀⟩ := hupper.exists
  have hp2_plus_pos : 0 < p.2 + 1 := by
    have hxinv_pos : 0 < 1 / (x n₀).1 := one_div_pos.mpr (hx_pos n₀)
    exact lt_trans hxinv_pos (lt_of_le_of_lt (hx_ineq n₀) hn₀)
  have hlower : ∀ᶠ n in Filter.atTop, 1 / (p.2 + 1) < (x n).1 := by
    filter_upwards [hupper] with n hn
    have hlt : 1 / (x n).1 < p.2 + 1 := lt_of_le_of_lt (hx_ineq n) hn
    exact (one_div_lt (hx_pos n) hp2_plus_pos).mp hlt
  have hp1_ge : 1 / (p.2 + 1) ≤ p.1 := by
    apply isClosed_Ici.mem_of_tendsto hp₁
    exact hlower.mono fun n hn ↦ hn.le
  have hp1_pos : 0 < p.1 := lt_of_lt_of_le (one_div_pos.mpr hp2_plus_pos) hp1_ge
  -- Continuity of inversion on `(0, ∞)` lets us pass the reciprocal inequality to the limit.
  have hrecip : Filter.Tendsto (fun n ↦ 1 / (x n).1) Filter.atTop (nhds (1 / p.1)) := by
    simpa [one_div] using hp₁.inv₀ (ne_of_gt hp1_pos)
  have hpineq : 1 / p.1 ≤ p.2 := by
    have hpair :
        Filter.Tendsto (fun n ↦ (1 / (x n).1, (x n).2)) Filter.atTop (nhds (1 / p.1, p.2)) :=
      hrecip.prodMk_nhds hp₂
    have hmem :
        ∀ᶠ n in Filter.atTop, (1 / (x n).1, (x n).2) ∈ {q : ℝ × ℝ | q.1 ≤ q.2} :=
      Filter.Eventually.of_forall hx_ineq
    exact (isClosed_le continuous_fst continuous_snd).mem_of_tendsto hpair hmem
  exact (mem_reciprocalEpigraphOnPositiveRay_iff p).mpr ⟨hp1_pos, by simpa [ge_iff_le] using hpineq⟩

/-- The Chapter 2 owner set `reciprocalEpigraphOnPositiveRay` is closed in `ℝ²`. -/
-- Proof sketch: the bridge theorem identifies this set with
-- `effectiveEpigraph positiveReciprocalExtension`; rewrite and apply
-- `lowerSemicontinuous_positiveReciprocalExtension`.
theorem reciprocalEpigraphOnPositiveRay_isClosed :
    IsClosed reciprocalEpigraphOnPositiveRay := by
  -- On `ℝ × ℝ`, sequential closedness is equivalent to closedness.
  exact (isSeqClosed_iff_isClosed).mp reciprocalEpigraphOnPositiveRay_isSeqClosed

/-- Proposition 3.5 (3): the effective domain of the extended reciprocal is exactly `(0, ∞)`. -/
-- Proof sketch: unfold `positiveReciprocalExtension`; for `x > 0` the value is the finite real
-- `1 / x`, while for `x ≤ 0` the value is `⊤`; equivalently, identify `dom` with `Set.Ioi 0`.
theorem positiveReciprocalExtension_effectiveDomain_eq_Ioi :
    dom positiveReciprocalExtension = Set.Ioi 0 := by
  -- The domain-membership helper turns the set equality into the defining positivity condition.
  ext x
  exact positiveReciprocalExtension_mem_dom_iff x

/-- Proposition 3.5 (4): the effective domain of the extended reciprocal is an open subset of
`ℝ`. -/
-- Proof sketch: rewrite the domain using
-- `positiveReciprocalExtension_effectiveDomain_eq_Ioi` and use `isOpen_Ioi`.
theorem isOpen_positiveReciprocalExtension_effectiveDomain :
    IsOpen (dom positiveReciprocalExtension) := by
  -- Once the effective domain is identified with `(0, ∞)`, openness is immediate.
  rw [positiveReciprocalExtension_effectiveDomain_eq_Ioi]
  simpa using isOpen_Ioi

end
