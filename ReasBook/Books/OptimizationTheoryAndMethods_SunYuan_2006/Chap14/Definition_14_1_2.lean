/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Operator.NNNorm
import Mathlib.Data.Set.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.LocallyLipschitzAt
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_1_extra_1

noncomputable section

-- Domain sampling:
-- * primary domain: Clarke generalized differentials on real normed spaces
-- * sampled chapter owners: `clarkeDirectionalDerivWithin`, `LocallyLipschitzAt`
-- * sampled ambient/project owners: `StrongDual`, `ContinuousLinearMap.sSup_unitClosedBall_eq_norm`
-- * core/canonical owner reused here: `clarkeDirectionalDerivWithin`
-- * source-facing layer here: the whole-space specialization in Definition 14.1.2
-- * primitive data: the domain-sensitive Clarke owner from `Definition_14_1_extra_1`
-- * derived API here: the `Set.univ` bridge, the whole-space Clarke differential, and the
--   local-Lipschitz real-valued bridge from the canonical `EReal`-valued owner

section

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

local notation "DualSpace" => StrongDual ℝ E

/-- The Clarke generalized directional derivative of `f` at `x` in direction `d` is the joint
limsup of the difference quotient as `y → x` and `t → 0` through positive scalars.
This whole-space owner is the `Set.univ` specialization of the domain-sensitive owner
`clarkeDirectionalDerivWithin`, so its codomain is `EReal`; later theorem layers recover the
finite real-valued textbook formulas under local Lipschitz hypotheses. -/
abbrev clarkeDirectionalDeriv (f : E → ℝ) (x d : E) : EReal :=
  clarkeDirectionalDerivWithin Set.univ f ⟨x, by simp⟩ d

scoped[ClarkeDirectionalDerivative] notation:max f:max "ᵒ(" x "; " d ")" =>
  clarkeDirectionalDeriv f x d

open scoped ClarkeDirectionalDerivative

/-- Unfolding formula for `clarkeDirectionalDeriv` as the `Set.univ` specialization of
`clarkeDirectionalDerivWithin`. -/
theorem clarkeDirectionalDeriv_eq_limsup (f : E → ℝ) (x d : E) :
    fᵒ(x; d) =
      Filter.limsup
        (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
        (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)) := by
  simpa [clarkeDirectionalDeriv] using
    clarkeDirectionalDerivWithin_eq_limsup Set.univ f ⟨x, by simp⟩ d

/-- Helper for Chapter14 Definition 14.1.2: the whole-space Clarke pair filter is nontrivial,
because positive times approach `0` in the second coordinate while the first coordinate stays at
`x`. -/
lemma wholeSpaceClarkePairFilter_neBot (x d : E) :
    (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)).NeBot := by
  let s : Set (E × ℝ) := clarkeDirectionalDerivWithinDomain Set.univ d
  -- Normalize the whole-space domain to the simple positivity condition on the time coordinate.
  have hs : s = {p : E × ℝ | 0 < p.2} := by
    ext p
    simp [s, clarkeDirectionalDerivWithinDomain]
  rw [show nhdsWithin ((x : E), (0 : ℝ)) s =
      nhdsWithin ((x : E), (0 : ℝ)) {p : E × ℝ | 0 < p.2} by simp [hs]]
  refine (mem_closure_iff_nhdsWithin_neBot.1 ?_)
  rw [Metric.mem_closure_iff]
  intro ε hε
  -- Choose the pair `(x, ε / 2)` to stay in every neighborhood of `(x, 0)` while keeping
  -- positive time.
  refine ⟨(x, ε / 2), by simpa using show (0 : ℝ) < ε / 2 by linarith, ?_⟩
  rw [Prod.dist_eq, dist_self, max_lt_iff, Real.dist_eq]
  constructor
  · exact hε
  · rw [zero_sub, abs_of_nonpos (by linarith)]
    linarith

/-- Helper for Chapter14 Definition 14.1.2: along the whole-space Clarke pair filter, both
endpoints of the difference quotient eventually remain inside any closed ball centered at `x`. -/
lemma eventuallyMemClosedBallEndpoints_of_closedBallLipschitz
    (x d : E) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d),
      p.1 ∈ Metric.closedBall x ε ∧ p.1 + p.2 • d ∈ Metric.closedBall x ε := by
  have hfst :
      Prod.fst ⁻¹' Metric.closedBall x ε ∈ nhds ((x : E), (0 : ℝ)) := by
    simpa using
      (continuous_fst.continuousAt.preimage_mem_nhds
        (show Metric.closedBall x ε ∈ nhds (((x : E), (0 : ℝ)).1) by
          simpa using (Metric.closedBall_mem_nhds x hε)))
  have hstep_cont : Continuous fun p : E × ℝ ↦ p.1 + p.2 • d := by
    exact continuous_fst.add (continuous_snd.smul continuous_const)
  have hstep :
      (fun p : E × ℝ ↦ p.1 + p.2 • d) ⁻¹' Metric.closedBall x ε ∈ nhds ((x : E), (0 : ℝ)) := by
    simpa using
      (hstep_cont.continuousAt.preimage_mem_nhds
        (show Metric.closedBall x ε ∈ nhds (((x : E), (0 : ℝ)).1 + (((x : E), (0 : ℝ)).2) • d) by
          simpa using (Metric.closedBall_mem_nhds x hε)))
  -- Restrict both neighborhood facts from `nhds` to the Clarke within-filter.
  filter_upwards [nhdsWithin_le_nhds hfst, nhdsWithin_le_nhds hstep] with p hp₁ hp₂
  exact ⟨hp₁, hp₂⟩

/-- Helper for Chapter14 Definition 14.1.2: a closed-ball Lipschitz bound controls the absolute
value of the Clarke difference quotient by `(K : ℝ) * ‖d‖` on the whole-space pair filter. -/
lemma eventuallyAbsClarkeQuotient_le_of_closedBallLipschitz
    (f : E → ℝ) (x d : E) (K : NNReal) {ε : ℝ} (hε : 0 < ε)
    (hK : LipschitzOnWith K f (Metric.closedBall x ε)) :
    ∀ᶠ p in
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d),
      |(f (p.1 + p.2 • d) - f p.1) / p.2| ≤ (K : ℝ) * ‖d‖ := by
  -- Combine endpoint control with the domain condition `0 < p.2`.
  filter_upwards
      [eventuallyMemClosedBallEndpoints_of_closedBallLipschitz x d hε, self_mem_nhdsWithin] with
      p hp_mem hp_domain
  have hp2 : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hp_domain).2.1
  have hp2_ne : p.2 ≠ 0 := ne_of_gt hp2
  have hdist_enn := hK hp_mem.2 hp_mem.1
  have hdist :
      ‖f (p.1 + p.2 • d) - f p.1‖ ≤ (K : ℝ) * ‖p.2 • d‖ := by
    have hdist_ofReal :
        ENNReal.ofReal (‖f (p.1 + p.2 • d) - f p.1‖) ≤
          ENNReal.ofReal ((K : ℝ) * ‖p.2 • d‖) := by
      simpa [edist_dist, dist_eq_norm, ENNReal.ofReal_mul, K.2] using hdist_enn
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hdist_ofReal
  have hnorm_div :
      ‖f (p.1 + p.2 • d) - f p.1‖ / p.2 ≤ (K : ℝ) * ‖d‖ := by
    calc
      ‖f (p.1 + p.2 • d) - f p.1‖ / p.2 ≤ ((K : ℝ) * ‖p.2 • d‖) / p.2 := by
        exact div_le_div_of_nonneg_right hdist hp2.le
      _ = ((K : ℝ) * (p.2 * ‖d‖)) / p.2 := by
        rw [norm_smul, Real.norm_of_nonneg hp2.le]
      _ = (K : ℝ) * ‖d‖ := by
        field_simp [hp2_ne]
  -- Rewrite the absolute-value quotient to a norm quotient and apply the Lipschitz estimate.
  calc
    |(f (p.1 + p.2 • d) - f p.1) / p.2| =
        ‖f (p.1 + p.2 • d) - f p.1‖ / p.2 := by
          rw [abs_div, abs_of_pos hp2, ← Real.norm_eq_abs]
    _ ≤ (K : ℝ) * ‖d‖ := hnorm_div

/-- Helper for Chapter14 Definition 14.1.2: a closed-ball Lipschitz witness gives finite lower
and upper `EReal` bounds for the whole-space Clarke directional derivative. -/
lemma clarkeDirectionalDeriv_bounds_of_closedBallLipschitz
    (f : E → ℝ) (x d : E) (K : NNReal)
    (hK : ∃ ε : ℝ, 0 < ε ∧ LipschitzOnWith K f (Metric.closedBall x ε)) :
    (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ fᵒ(x; d)) ∧
      (fᵒ(x; d) ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal)) := by
  rcases hK with ⟨ε, hε, hLip⟩
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let q : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
  have habs :
      ∀ᶠ p in l, |(f (p.1 + p.2 • d) - f p.1) / p.2| ≤ (K : ℝ) * ‖d‖ := by
    simpa [l] using
      eventuallyAbsClarkeQuotient_le_of_closedBallLipschitz f x d K hε hLip
  have hupper_event : ∀ᶠ p in l, q p ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal) := by
    -- The absolute-value estimate gives the eventual upper real bound, then we coerce to `EReal`.
    filter_upwards [habs] with p hp
    change (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal) ≤
      (((K : ℝ) * ‖d‖ : ℝ) : EReal)
    exact_mod_cast (abs_le.mp hp).2
  have hlower_event :
      ∀ᶠ p in l, (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ q p) := by
    -- The same absolute-value estimate also yields the eventual lower real bound.
    filter_upwards [habs] with p hp
    change (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤
      (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    exact_mod_cast (abs_le.mp hp).1
  have hupper : Filter.limsup q l ≤ (((K : ℝ) * ‖d‖ : ℝ) : EReal) := by
    exact Filter.limsup_le_of_le
      (f := l) (u := q) (a := (((K : ℝ) * ‖d‖ : ℝ) : EReal)) (h := hupper_event)
  have hbounded : l.IsBoundedUnder (· ≤ ·) q := ⟨(((K : ℝ) * ‖d‖ : ℝ) : EReal), hupper_event⟩
  have hlower : (((-((K : ℝ) * ‖d‖) : ℝ) : EReal) ≤ Filter.limsup q l) := by
    refine Filter.le_limsup_of_le
      (f := l) (u := q) (a := (((-((K : ℝ) * ‖d‖) : ℝ) : EReal))) (hf := hbounded) ?_
    intro b hb
    rcases hl_ne.nonempty_of_mem (Filter.inter_mem hlower_event hb) with ⟨p, hp⟩
    exact le_trans hp.1 hp.2
  -- Translate the limsup sandwich back to the whole-space Clarke owner.
  rw [clarkeDirectionalDeriv_eq_limsup]
  exact ⟨by simpa [l, q] using hlower, by simpa [l, q] using hupper⟩

/-- If `f` is Lipschitz near `x`, then the whole-space Clarke directional derivative is finite in
every direction. This keeps the canonical owner `fᵒ(x; d) : EReal` primary, while exposing the
finiteness hypothesis at theorem level instead of hiding it in an unconditional real-valued
wrapper. -/
theorem clarkeDirectionalDeriv_ne_top_ne_bot_of_locallyLipschitzAt
    (f : E → ℝ) (x d : E) (h_local : LocallyLipschitzAt f x) :
    fᵒ(x; d) ≠ ⊤ ∧ fᵒ(x; d) ≠ ⊥ := by
  rcases locallyLipschitzAt_iff.mp h_local with ⟨ε, hε, K, hLip⟩
  -- The local closed-ball Lipschitz witness yields a finite `EReal` sandwich for `fᵒ(x; d)`.
  obtain ⟨hlower, hupper⟩ :=
    clarkeDirectionalDeriv_bounds_of_closedBallLipschitz f x d K ⟨ε, hε, hLip⟩
  constructor
  · -- A finite upper bound places `fᵒ(x; d)` strictly below `⊤`.
    exact (lt_of_le_of_lt hupper (EReal.coe_lt_top ((K : ℝ) * ‖d‖))).ne
  · -- A finite lower bound places `fᵒ(x; d)` strictly above `⊥`.
    exact (lt_of_lt_of_le (EReal.bot_lt_coe (-((K : ℝ) * ‖d‖))) hlower).ne'

/-- Under a local Lipschitz hypothesis, the real-valued textbook Clarke directional derivative is
obtained by applying `EReal.toReal` to the canonical owner `fᵒ(x; d)`. -/
abbrev clarkeDirectionalDerivReal (f : E → ℝ) (x d : E) : ℝ :=
  (fᵒ(x; d)).toReal

/-- Under a local Lipschitz hypothesis, the real-valued textbook Clarke directional derivative is
obtained by applying `EReal.toReal` to the canonical owner `fᵒ(x; d)`. -/
@[simp] theorem coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
    (f : E → ℝ) (x d : E) (h_local : LocallyLipschitzAt f x) :
    ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) = fᵒ(x; d) := by
  obtain ⟨h_top, h_bot⟩ :=
    clarkeDirectionalDeriv_ne_top_ne_bot_of_locallyLipschitzAt f x d h_local
  simpa using (EReal.coe_toReal h_top h_bot)

/-- Chapter14 Definition 14.1.2 (1): if `f` is Lipschitz near `x`, encoded by a hypothesis
`LocallyLipschitzAt f x`, the generalized differential (Clarke differential) of `f` at `x` is
the set of continuous linear functionals `ξ` such that the `EReal`-valued Clarke directional
derivative dominates the pairing `ξ d` in every direction `d`. Under local Lipschitz
hypotheses this is the textbook Clarke differential, while the `EReal` codomain keeps the raw
whole-space owner canonical outside that regime. An element of `(∂ᶜ f) x` is a generalized
gradient at `x`. -/
def clarkeDifferential (f : E → ℝ) (x : E) : Set DualSpace :=
  {ξ | ∀ d : E, ξ d ≤ fᵒ(x; d)}

scoped[ClarkeDifferential] prefix:100 "∂ᶜ " => clarkeDifferential

open scoped ClarkeDifferential

/-- Membership in `(∂ᶜ f) x` is exactly the source inequality `fᵒ(x; d) ≥ ξ d` for every
direction `d`. -/
theorem mem_clarkeDifferential_iff (f : E → ℝ) (x : E) (ξ : DualSpace) :
    ξ ∈ (∂ᶜ f) x ↔ ∀ d : E, ξ d ≤ fᵒ(x; d) := Iff.rfl

/- Chapter14 Definition 14.1.2 (2): recall the canonical operator-norm theorem on the dual space;
for `ξ : StrongDual ℝ E`, this is the standard closed-unit-ball formula for `‖ξ‖`. -/
#check ContinuousLinearMap.sSup_unitClosedBall_eq_norm

#print axioms clarkeDirectionalDeriv
#print axioms clarkeDifferential

end
