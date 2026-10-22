/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap05.section24_part5

section Chap05
section Section24

open scoped ConvexAnalysis

attribute [local instance] Classical.propDecidable

/-- Helper for Proposition 5.24.4: the `m = 1` case of cyclic monotonicity is exactly the
two-point cross-term inequality used in the monotonicity proof. -/
lemma helperForProposition_5_24_4_twoPointCycle_rawInequality {n : ℕ}
    {ρ : (Fin n → ℝ) → Set (Fin n → ℝ)} (hρ : IsCyclicallyMonotone ρ)
    {x0 x1 x0Star x1Star : Fin n → ℝ}
    (hx0Star : x0Star ∈ ρ x0) (hx1Star : x1Star ∈ ρ x1) :
    dotProduct x1 x0Star + dotProduct x0 x1Star ≤ dotProduct x0 x0Star + dotProduct x1 x1Star := by
  have hmem : ∀ i : Fin (1 + 1), ![x0Star, x1Star] i ∈ ρ (![x0, x1] i) := by
    intro i
    -- The two cycle vertices are exactly the given graph points.
    fin_cases i
    · simpa using hx0Star
    · simpa using hx1Star
  have hcycle := hρ 1 ![x0, x1] ![x0Star, x1Star] hmem
  -- Expanding the `Fin 2` cycle yields the textbook raw inequality.
  simpa using hcycle

/-- Helper for Proposition 5.24.4: the raw two-point cycle inequality rearranges to the standard
monotonicity inequality. -/
lemma helperForProposition_5_24_4_rearrange_rawCycle_to_monotone {n : ℕ}
    {x0 x1 x0Star x1Star : Fin n → ℝ}
    (hraw :
      dotProduct x1 x0Star + dotProduct x0 x1Star ≤
        dotProduct x0 x0Star + dotProduct x1 x1Star) :
    0 ≤ dotProduct (x1 - x0) (x1Star - x0Star) := by
  have hle : dotProduct (x1 - x0) x0Star ≤ dotProduct (x1 - x0) x1Star := by
    have hdiff :
        dotProduct x1 x0Star - dotProduct x0 x0Star ≤
          dotProduct x1 x1Star - dotProduct x0 x1Star := by
      -- Move the cross terms to opposite sides to isolate the same linear factor.
      linarith
    -- Rewrite both sides as dot products against the common displacement `x1 - x0`.
    simpa [dotProduct_sub, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hdiff
  -- Expanding the second factor difference turns the comparison into monotonicity.
  simpa [dotProduct_sub] using hle

/-- Proposition 5.24.4: Every cyclically monotone mapping is in particular a monotone mapping. -/
theorem IsCyclicallyMonotone.isMonotoneMultivaluedMapping {n : ℕ}
    {ρ : (Fin n → ℝ) → Set (Fin n → ℝ)} (hρ : IsCyclicallyMonotone ρ) :
    IsMonotoneMultivaluedMapping ρ := by
  intro x0 x1 x0Star x1Star hx0Star hx1Star
  -- Specialize cyclic monotonicity to the two-point cycle through the given graph points.
  have hraw :=
    helperForProposition_5_24_4_twoPointCycle_rawInequality hρ hx0Star hx1Star
  -- The raw cycle inequality is equivalent to the usual monotonicity inequality.
  exact helperForProposition_5_24_4_rearrange_rawCycle_to_monotone hraw

/-- A subset of `ℝ²` is coordinatewise totally ordered when any two distinct points in it are
comparable for the product partial order. -/
def IsCoordinatewiseTotallyOrdered (Γ : Set (ℝ × ℝ)) : Prop :=
  Γ.Pairwise (fun p q => p ≤ q ∨ q ≤ p)

/-- A subset of `ℝ²` is maximal coordinatewise totally ordered when it is coordinatewise totally
ordered and admits no strictly larger coordinatewise totally ordered superset. -/
def IsMaximalCoordinatewiseTotallyOrdered (Γ : Set (ℝ × ℝ)) : Prop :=
  IsCoordinatewiseTotallyOrdered Γ ∧
    ∀ ⦃Δ : Set (ℝ × ℝ)⦄, Γ ⊆ Δ → IsCoordinatewiseTotallyOrdered Δ → Δ = Γ

/-- The lower boundary profile attached to a coordinatewise totally ordered subset `Γ ⊆ ℝ²`,
obtained as the supremum of the second coordinates strictly to the left of the base point. -/
noncomputable def maximalCoordinatewiseLowerProfile (Γ : Set (ℝ × ℝ)) : ℝ → EReal :=
  fun x =>
    sSup {y : EReal | ∃ p ∈ Γ, p.1 < x ∧ y = ((p.2 : ℝ) : EReal)}

/-- The upper boundary profile attached to a coordinatewise totally ordered subset `Γ ⊆ ℝ²`,
obtained as the infimum of the second coordinates strictly to the right of the base point. -/
noncomputable def maximalCoordinatewiseUpperProfile (Γ : Set (ℝ × ℝ)) : ℝ → EReal :=
  fun x =>
    sInf {y : EReal | ∃ p ∈ Γ, x < p.1 ∧ y = ((p.2 : ℝ) : EReal)}

/-- The lower boundary profile of a coordinatewise chain is monotone. -/
lemma maximalCoordinatewiseLowerProfile_monotone
    {Γ : Set (ℝ × ℝ)} :
    Monotone (maximalCoordinatewiseLowerProfile Γ) := by
  intro x y hxy
  refine sSup_le ?_
  intro v hv
  rcases hv with ⟨p, hpΓ, hpx, rfl⟩
  exact le_sSup ⟨p, hpΓ, lt_of_lt_of_le hpx hxy, rfl⟩

/-- If a monotone profile never takes finite values, then every value is either `⊤` or `⊥`. -/
lemma helperForRemark_5_24_3_allValues_top_or_bot_of_no_finiteWitness
    (φ : ℝ → EReal)
    (hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)) :
    ∀ x : ℝ, φ x = (⊤ : EReal) ∨ φ x = (⊥ : EReal) := by
  intro x
  by_cases htop : φ x = (⊤ : EReal)
  · exact Or.inl htop
  · by_cases hbot : φ x = (⊥ : EReal)
    · exact Or.inr hbot
    · exfalso
      exact hNoFinite ⟨x, htop, hbot⟩

/-- A nonempty complete-curve band coming from a monotone profile with no finite values is a
single vertical line. -/
lemma helperForRemark_5_24_3_band_eq_verticalLine_of_no_finiteWitness
    (Γ : Set (ℝ × ℝ)) (φ : ℝ → EReal) (hmono : Monotone φ)
    (hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal))
    (hΓnonempty : Γ.Nonempty)
    (hΓdef :
      Γ = {p : ℝ × ℝ |
        leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
          (p.2 : EReal) ≤ rightLimitProfile φ p.1}) :
    ∃ a : ℝ, Γ = {p : ℝ × ℝ | p.1 = a} := by
  rcases hΓnonempty with ⟨p0, hp0Γ⟩
  have hTB := helperForRemark_5_24_3_allValues_top_or_bot_of_no_finiteWitness φ hNoFinite
  have hp0Band :
      leftLimitProfile φ p0.1 ≤ (p0.2 : EReal) ∧
        (p0.2 : EReal) ≤ rightLimitProfile φ p0.1 := by
    simpa [hΓdef] using hp0Γ
  have hleftVal : ∀ z : ℝ, z < p0.1 → φ z = (⊥ : EReal) := by
    intro z hz
    rcases hTB z with htop | hbot
    · have htopLe : (⊤ : EReal) ≤ leftLimitProfile φ p0.1 := by
        simpa [htop] using (le_sSup ⟨z, hz, rfl⟩ :
          φ z ≤ leftLimitProfile φ p0.1)
      have : (⊤ : EReal) ≤ ((p0.2 : ℝ) : EReal) := le_trans htopLe hp0Band.1
      simp at this
    · exact hbot
  have hrightVal : ∀ z : ℝ, p0.1 < z → φ z = (⊤ : EReal) := by
    intro z hz
    rcases hTB z with htop | hbot
    · exact htop
    · have hrightLeBot : rightLimitProfile φ p0.1 ≤ (⊥ : EReal) := by
        simpa [hbot] using (sInf_le ⟨z, hz, rfl⟩ :
          rightLimitProfile φ p0.1 ≤ φ z)
      have : ((p0.2 : ℝ) : EReal) ≤ (⊥ : EReal) := le_trans hp0Band.2 hrightLeBot
      simp at this
  have hleftEq : leftLimitProfile φ p0.1 = (⊥ : EReal) := by
    apply le_antisymm
    · refine sSup_le ?_
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      simp [hleftVal z hz]
    · exact bot_le
  have hrightEq : rightLimitProfile φ p0.1 = (⊤ : EReal) := by
    apply le_antisymm
    · exact le_top
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨z, hz, rfl⟩
      simp [hrightVal z hz]
  refine ⟨p0.1, ?_⟩
  ext p
  constructor
  · intro hpΓ
    have hpBand :
        leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
          (p.2 : EReal) ≤ rightLimitProfile φ p.1 := by
      simpa [hΓdef] using hpΓ
    by_contra hpNe
    rcases lt_or_gt_of_ne hpNe with hpLt | hpGt
    · let z : ℝ := (p.1 + p0.1) / 2
      have hpz : p.1 < z := by
        dsimp [z]
        linarith
      have hz0 : z < p0.1 := by
        dsimp [z]
        linarith
      have hrightLeBot : rightLimitProfile φ p.1 ≤ (⊥ : EReal) := by
        simpa [hleftVal z hz0] using (sInf_le ⟨z, hpz, rfl⟩ :
          rightLimitProfile φ p.1 ≤ φ z)
      have : ((p.2 : ℝ) : EReal) ≤ (⊥ : EReal) := le_trans hpBand.2 hrightLeBot
      simp at this
    · let z : ℝ := (p0.1 + p.1) / 2
      have h0z : p0.1 < z := by
        dsimp [z]
        linarith
      have hzp : z < p.1 := by
        dsimp [z]
        linarith
      have htopLe : (⊤ : EReal) ≤ leftLimitProfile φ p.1 := by
        simpa [hrightVal z h0z] using (le_sSup ⟨z, hzp, rfl⟩ :
          φ z ≤ leftLimitProfile φ p.1)
      have : (⊤ : EReal) ≤ ((p.2 : ℝ) : EReal) := le_trans htopLe hpBand.1
      simp at this
  · intro hp1
    rcases p with ⟨x, y⟩
    have hx : x = p0.1 := by simpa using hp1
    subst hx
    have hpBand :
        leftLimitProfile φ p0.1 ≤ (y : EReal) ∧
          (y : EReal) ≤ rightLimitProfile φ p0.1 := by
      simp [hleftEq, hrightEq]
    simpa [hΓdef] using hpBand

/-- For a monotone profile, the value at `x` always lies between the left and right limit
profiles. -/
lemma helperForRemark_5_24_3_leftLimitProfile_le_value_le_rightLimitProfile
    (φ : ℝ → EReal) (hmono : Monotone φ) (x : ℝ) :
    leftLimitProfile φ x ≤ φ x ∧ φ x ≤ rightLimitProfile φ x := by
  constructor
  · refine sSup_le ?_
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hmono (le_of_lt hz)
  · refine le_sInf ?_
    intro y hy
    rcases hy with ⟨z, hz, rfl⟩
    exact hmono (le_of_lt hz)

/-- A finite value of a monotone profile gives a real graph point on the associated band. -/
lemma helperForRemark_5_24_3_mem_band_of_finite_value
    (φ : ℝ → EReal) (hmono : Monotone φ) {x : ℝ}
    (hxTop : φ x ≠ (⊤ : EReal)) (hxBot : φ x ≠ (⊥ : EReal)) :
    (x, (φ x).toReal) ∈ {p : ℝ × ℝ |
      leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
        (p.2 : EReal) ≤ rightLimitProfile φ p.1} := by
  have hband := helperForRemark_5_24_3_leftLimitProfile_le_value_le_rightLimitProfile φ hmono x
  have hcoe : (((φ x).toReal : ℝ) : EReal) = φ x := EReal.coe_toReal hxTop hxBot
  simpa [hcoe] using hband

/-- A vertical line is a maximal coordinatewise totally ordered subset of `ℝ²`. -/
lemma helperForRemark_5_24_3_verticalLine_isMaximalCoordinatewiseTotallyOrdered
    (a : ℝ) :
    IsMaximalCoordinatewiseTotallyOrdered {p : ℝ × ℝ | p.1 = a} := by
  refine ⟨?_, ?_⟩
  · intro p hp q hq hpq
    have hp1 : p.1 = a := hp
    have hq1 : q.1 = a := hq
    rcases le_total p.2 q.2 with hpq2 | hqp2
    · exact Or.inl ⟨by simpa [hp1, hq1], hpq2⟩
    · exact Or.inr ⟨by simpa [hp1, hq1], hqp2⟩
  · intro Δ hsubset hΔOrdered
    ext p
    constructor
    · intro hpΔ
      by_cases hp1 : p.1 = a
      · simpa [hp1]
      · rcases lt_or_gt_of_ne hp1 with hpLt | hpGt
        · have hqΓ : (a, p.2 - 1) ∈ {q : ℝ × ℝ | q.1 = a} := by simp
          have hqΔ : (a, p.2 - 1) ∈ Δ := hsubset hqΓ
          have hcomp := hΔOrdered hqΔ hpΔ (by
            intro hEq
            exact hp1 (by simpa using (congrArg Prod.fst hEq).symm))
          cases hcomp with
          | inl hle =>
              have : ¬ a ≤ p.1 := not_le_of_gt hpLt
              exact (this hle.1).elim
          | inr hle =>
              have : ¬ p.2 ≤ p.2 - 1 := by linarith
              exact (this hle.2).elim
        · have hqΓ : (a, p.2 + 1) ∈ {q : ℝ × ℝ | q.1 = a} := by simp
          have hqΔ : (a, p.2 + 1) ∈ Δ := hsubset hqΓ
          have hcomp := hΔOrdered hqΔ hpΔ (by
            intro hEq
            exact hp1 (by simpa using (congrArg Prod.fst hEq).symm))
          cases hcomp with
          | inl hle =>
              have : ¬ p.2 + 1 ≤ p.2 := by linarith
              exact (this hle.2).elim
          | inr hle =>
              have : ¬ p.1 ≤ a := not_le_of_gt hpGt
              exact (this hle.1).elim
    · intro hpΓ
      exact hsubset hpΓ

/-- If `β` is the left boundary of the `⊤`-region of a monotone profile, then every point to the
right of `β` already has value `⊤`. -/
lemma helperForRemark_5_24_3_eq_top_of_lt_sInf_topRegion
    (φ : ℝ → EReal) (hmono : Monotone φ) {β z : ℝ}
    (hz : β < z)
    (hβ :
      β = sInf {t : ℝ | φ t = (⊤ : EReal)})
    (hTopBddBelow : BddBelow ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ))
    (hTopNonempty : ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ).Nonempty) :
    φ z = (⊤ : EReal) := by
  have hsInf_lt :
      sInf {t : ℝ | φ t = (⊤ : EReal)} < z := by
    simpa [hβ] using hz
  have hsInf_lt_iff :
      sInf ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ) < z ↔
        ∃ u ∈ ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ), u < z := by
    simpa using
      (csInf_lt_iff hTopBddBelow hTopNonempty :
        sInf ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ) < z ↔
          ∃ u ∈ ({t : ℝ | φ t = (⊤ : EReal)} : Set ℝ), u < z)
  obtain ⟨u, huTop, huz⟩ := hsInf_lt_iff.1 hsInf_lt
  have hle : (⊤ : EReal) ≤ φ z := by
    have huTop' : φ u = (⊤ : EReal) := huTop
    have : φ u ≤ φ z := hmono (le_of_lt huz)
    simpa [huTop'] using this
  exact top_le_iff.mp hle

/-- If `α` is the right boundary of the `⊥`-region of a monotone profile, then every point to the
left of `α` already has value `⊥`. -/
lemma helperForRemark_5_24_3_eq_bot_of_lt_sSup_botRegion
    (φ : ℝ → EReal) (hmono : Monotone φ) {α z : ℝ}
    (hz : z < α)
    (hα :
      α = sSup {t : ℝ | φ t = (⊥ : EReal)})
    (hBotBddAbove : BddAbove ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ))
    (hBotNonempty : ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ).Nonempty) :
    φ z = (⊥ : EReal) := by
  have hz_lt :
      z < sSup {t : ℝ | φ t = (⊥ : EReal)} := by
    simpa [hα] using hz
  have hlt_sSup_iff :
      z < sSup ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ) ↔
        ∃ u ∈ ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ), z < u := by
    simpa using
      (lt_csSup_iff hBotBddAbove hBotNonempty :
        z < sSup ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ) ↔
          ∃ u ∈ ({t : ℝ | φ t = (⊥ : EReal)} : Set ℝ), z < u)
  obtain ⟨u, huBot, hzu⟩ := hlt_sSup_iff.1 hz_lt
  have hle : φ z ≤ (⊥ : EReal) := by
    have huBot' : φ u = (⊥ : EReal) := huBot
    have : φ z ≤ φ u := hmono (le_of_lt hzu)
    simpa [huBot'] using this
  exact le_bot_iff.mp hle

/-- The band between the left and right limit profiles of a monotone scalar function is
coordinatewise totally ordered. -/
lemma helperForRemark_5_24_3_band_isCoordinatewiseTotallyOrdered
    (φ : ℝ → EReal) (hmono : Monotone φ) :
    IsCoordinatewiseTotallyOrdered
      {p : ℝ × ℝ |
        leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
          (p.2 : EReal) ≤ rightLimitProfile φ p.1} := by
  intro p hp q hq hpq
  rcases lt_trichotomy p.1 q.1 with hpq1 | hpq1 | hqp1
  · left
    refine ⟨le_of_lt hpq1, ?_⟩
    let z : ℝ := (p.1 + q.1) / 2
    have hpz : p.1 < z := by
      dsimp [z]
      linarith
    have hzq : z < q.1 := by
      dsimp [z]
      linarith
    have hRightLeft :
        rightLimitProfile φ p.1 ≤ leftLimitProfile φ q.1 := by
      exact le_trans (sInf_le ⟨z, hpz, rfl⟩) (le_sSup ⟨z, hzq, rfl⟩)
    have hpq2E :
        ((p.2 : ℝ) : EReal) ≤ ((q.2 : ℝ) : EReal) := le_trans hp.2 (le_trans hRightLeft hq.1)
    exact_mod_cast hpq2E
  · have hpq1' : p.1 = q.1 := hpq1
    rcases le_total p.2 q.2 with hpq2 | hqp2
    · exact Or.inl ⟨hpq1'.le, hpq2⟩
    · exact Or.inr ⟨hpq1'.ge, hqp2⟩
  · right
    refine ⟨le_of_lt hqp1, ?_⟩
    let z : ℝ := (q.1 + p.1) / 2
    have hqz : q.1 < z := by
      dsimp [z]
      linarith
    have hzp : z < p.1 := by
      dsimp [z]
      linarith
    have hRightLeft :
        rightLimitProfile φ q.1 ≤ leftLimitProfile φ p.1 := by
      exact le_trans (sInf_le ⟨z, hqz, rfl⟩) (le_sSup ⟨z, hzp, rfl⟩)
    have hqp2E :
        ((q.2 : ℝ) : EReal) ≤ ((p.2 : ℝ) : EReal) := le_trans hq.2 (le_trans hRightLeft hp.1)
    exact_mod_cast hqp2E

/-- A maximal coordinatewise totally ordered subset of `ℝ²` is a complete non-decreasing
curve. -/
lemma helperForRemark_5_24_3_completeCurve_of_maximalCoordinatewiseTotallyOrdered
    (Γ : Set (ℝ × ℝ))
    (hΓMax : IsMaximalCoordinatewiseTotallyOrdered Γ) :
    IsCompleteNondecreasingCurve Γ := by
  rcases hΓMax with ⟨hordered, hmaximal⟩
  let lower : ℝ → EReal := maximalCoordinatewiseLowerProfile Γ
  let upper : ℝ → EReal := maximalCoordinatewiseUpperProfile Γ
  have hlowerMono : Monotone lower := maximalCoordinatewiseLowerProfile_monotone
  have hLowerLeUpper : ∀ x : ℝ, lower x ≤ upper x := by
    intro x
    refine sSup_le ?_
    intro y hy
    rcases hy with ⟨p, hpΓ, hpx, rfl⟩
    refine le_sInf ?_
    intro z hz
    rcases hz with ⟨q, hqΓ, hxq, rfl⟩
    have hneq : p ≠ q := by
      intro hEq
      have : p.1 < p.1 := by
        exact lt_of_lt_of_le hpx (hEq ▸ le_of_lt hxq)
      exact lt_irrefl _ this
    have hcomp := hordered hpΓ hqΓ hneq
    cases hcomp with
    | inl hle =>
        exact_mod_cast hle.2
    | inr hle =>
        exfalso
        exact (not_le_of_gt hxq) (le_trans hle.1 (le_of_lt hpx))
  have hmemBand_of_memΓ :
      ∀ p ∈ Γ, lower p.1 ≤ ((p.2 : ℝ) : EReal) ∧ ((p.2 : ℝ) : EReal) ≤ upper p.1 := by
    intro p hpΓ
    constructor
    · refine sSup_le ?_
      intro y hy
      rcases hy with ⟨q, hqΓ, hqp, rfl⟩
      have hneq : q ≠ p := by
        intro hEq
        exact (lt_irrefl p.1) <| hEq ▸ hqp
      have hcomp := hordered hqΓ hpΓ hneq
      cases hcomp with
      | inl hle =>
          exact_mod_cast hle.2
      | inr hle =>
          exfalso
          exact (not_le_of_gt hqp) hle.1
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨q, hqΓ, hpq, rfl⟩
      have hneq : p ≠ q := by
        intro hEq
        exact (lt_irrefl p.1) <| hEq ▸ hpq
      have hcomp := hordered hpΓ hqΓ hneq
      cases hcomp with
      | inl hle =>
          exact_mod_cast hle.2
      | inr hle =>
          exfalso
          exact (not_le_of_gt hpq) hle.1
  have hmemΓ_of_memBand :
      ∀ x y : ℝ,
        lower x ≤ ((y : ℝ) : EReal) →
          ((y : ℝ) : EReal) ≤ upper x →
            (x, y) ∈ Γ := by
    intro x y hlower hyupper
    let p : ℝ × ℝ := (x, y)
    have hInsertOrdered : IsCoordinatewiseTotallyOrdered (insert p Γ) := by
      intro a ha b hb hab
      by_cases ha' : a = p
      · subst ha'
        by_cases hb' : b = p
        · subst hb'
          exact False.elim (hab rfl)
        · have hbΓ : b ∈ Γ := by
            simpa [hb', Set.mem_insert_iff] using hb
          rcases lt_trichotomy b.1 x with hbx | hbx | hxb
          · right
            refine ⟨le_of_lt hbx, ?_⟩
            have hbLower :
                ((b.2 : ℝ) : EReal) ≤ lower x := by
              exact le_sSup ⟨b, hbΓ, hbx, rfl⟩
            exact_mod_cast le_trans hbLower hlower
          · subst hbx
            rcases le_total y b.2 with hyb | hby
            · exact Or.inl ⟨le_rfl, hyb⟩
            · exact Or.inr ⟨le_rfl, hby⟩
          · left
            refine ⟨le_of_lt hxb, ?_⟩
            have hUpperb :
                upper x ≤ ((b.2 : ℝ) : EReal) := by
              exact sInf_le ⟨b, hbΓ, hxb, rfl⟩
            exact_mod_cast le_trans hyupper hUpperb
      · have haΓ : a ∈ Γ := by
          simpa [ha', Set.mem_insert_iff] using ha
        by_cases hb' : b = p
        · subst hb'
          rcases lt_trichotomy a.1 x with hax | hax | hxa
          · left
            refine ⟨le_of_lt hax, ?_⟩
            have haLower :
                ((a.2 : ℝ) : EReal) ≤ lower x := by
              exact le_sSup ⟨a, haΓ, hax, rfl⟩
            exact_mod_cast le_trans haLower hlower
          · subst hax
            rcases le_total a.2 y with hay | hya
            · exact Or.inl ⟨le_rfl, hay⟩
            · exact Or.inr ⟨le_rfl, hya⟩
          · right
            refine ⟨le_of_lt hxa, ?_⟩
            have hUppera :
                upper x ≤ ((a.2 : ℝ) : EReal) := by
              exact sInf_le ⟨a, haΓ, hxa, rfl⟩
            exact_mod_cast le_trans hyupper hUppera
        · have hbΓ : b ∈ Γ := by
            simpa [hb', Set.mem_insert_iff] using hb
          exact hordered haΓ hbΓ hab
    have hEq : insert p Γ = Γ := by
      exact hmaximal (by intro q hq; exact Set.mem_insert_of_mem _ hq) hInsertOrdered
    have hpInsert : p ∈ insert p Γ := Set.mem_insert _ _
    simpa [hEq] using hpInsert
  have hLeftEq : leftLimitProfile lower = lower := by
    funext x
    apply le_antisymm
    · refine sSup_le ?_
      intro y hy
      rcases hy with ⟨z, hzx, rfl⟩
      exact hlowerMono (le_of_lt hzx)
    · exact le_of_forall_lt fun c hc => by
        obtain ⟨v, hv, hcv⟩ := lt_sSup_iff.mp hc
        rcases hv with ⟨p, hpΓ, hpx, rfl⟩
        let z : ℝ := (p.1 + x) / 2
        have hpz : p.1 < z := by
          dsimp [z]
          linarith
        have hzx : z < x := by
          dsimp [z]
          linarith
        have hzLower :
            ((p.2 : ℝ) : EReal) ≤ lower z := by
          exact le_sSup ⟨p, hpΓ, hpz, rfl⟩
        exact
          lt_sSup_iff.mpr
            ⟨lower z, ⟨z, hzx, rfl⟩, lt_of_lt_of_le hcv hzLower⟩
  have hRightEq : rightLimitProfile lower = upper := by
    funext x
    apply le_antisymm
    · refine le_sInf ?_
      intro y hy
      rcases hy with ⟨q, hqΓ, hxq, rfl⟩
      let z : ℝ := (x + q.1) / 2
      have hxz : x < z := by
        dsimp [z]
        linarith
      have hzq : z < q.1 := by
        dsimp [z]
        linarith
      have hLowerzLe :
          lower z ≤ ((q.2 : ℝ) : EReal) := by
        refine sSup_le ?_
        intro v hv
        rcases hv with ⟨p, hpΓ, hpz, rfl⟩
        have hneq : p ≠ q := by
          intro hEq
          exact (lt_irrefl q.1) <| lt_trans (hEq ▸ hpz) hzq
        have hcomp := hordered hpΓ hqΓ hneq
        cases hcomp with
        | inl hle =>
            exact_mod_cast hle.2
        | inr hle =>
            exfalso
            exact (not_le_of_gt hzq) (le_trans hle.1 (le_of_lt hpz))
      exact le_trans (sInf_le ⟨z, hxz, rfl⟩) hLowerzLe
    · by_cases hupperTop : upper x = (⊤ : EReal)
      · rw [hupperTop]
        have hzTop : ∀ z : ℝ, x < z → lower z = (⊤ : EReal) := by
          intro z hxz
          apply top_unique
          refine le_of_forall_lt ?_
          intro c hc
          by_cases hlowerTop : lower x = (⊤ : EReal)
          · have htopLe : (⊤ : EReal) ≤ lower z := by
              simpa [hlowerTop] using hlowerMono (le_of_lt hxz)
            exact lt_of_lt_of_le hc htopLe
          · obtain ⟨u0, hcu0, hu0Top⟩ := EReal.lt_iff_exists_real_btwn.1 hc
            let u : ℝ := max u0 (lower x).toReal + 1
            have hxu : lower x ≤ ((u : ℝ) : EReal) := by
              have hxtoReal : lower x ≤ (((lower x).toReal : ℝ) : EReal) :=
                EReal.le_coe_toReal hlowerTop
              have htoRealLe : (lower x).toReal ≤ u := by
                dsimp [u]
                have hmax : (lower x).toReal ≤ max u0 (lower x).toReal := le_max_right _ _
                linarith
              have huE : (((lower x).toReal : ℝ) : EReal) ≤ ((u : ℝ) : EReal) := by
                exact_mod_cast htoRealLe
              exact le_trans hxtoReal huE
            have hcu : c < ((u : ℝ) : EReal) := by
              have hu0u : u0 < u := by
                dsimp [u]
                have hmax : u0 ≤ max u0 (lower x).toReal := le_max_left _ _
                linarith
              have hu0uE : ((u0 : ℝ) : EReal) ≤ ((u : ℝ) : EReal) := by
                exact_mod_cast (le_of_lt hu0u)
              exact lt_of_lt_of_le hcu0 hu0uE
            have huBand :
                lower x ≤ ((u : ℝ) : EReal) ∧ (((u : ℝ) : EReal) ≤ upper x) := by
              constructor
              · exact hxu
              · simpa [hupperTop] using (le_of_lt hu0Top : ((u : ℝ) : EReal) ≤ (⊤ : EReal))
            have hpΓ : (x, u) ∈ Γ := hmemΓ_of_memBand x u huBand.1 huBand.2
            have huLower :
                ((u : ℝ) : EReal) ≤ lower z := by
              exact le_sSup ⟨(x, u), hpΓ, hxz, rfl⟩
            exact lt_of_lt_of_le hcu huLower
        have hRightTop : rightLimitProfile lower x = (⊤ : EReal) := by
          rw [rightLimitProfile, sInf_eq_top]
          intro y hy
          rcases hy with ⟨z, hxz, rfl⟩
          exact hzTop z hxz
        simpa [hRightTop]
      · by_cases hupperBot : upper x = (⊥ : EReal)
        · rw [hupperBot]
          exact bot_le
        · have hu : (((upper x).toReal : ℝ) : EReal) = upper x := by
            exact EReal.coe_toReal hupperTop hupperBot
          have hBandAtX :
              lower x ≤ ((upper x).toReal : EReal) ∧
                ((((upper x).toReal : ℝ) : EReal) ≤ upper x) := by
            constructor
            · simpa [hu] using hLowerLeUpper x
            · simpa [hu]
          have hpΓ : (x, (upper x).toReal) ∈ Γ :=
            hmemΓ_of_memBand x (upper x).toReal hBandAtX.1 hBandAtX.2
          rw [← hu]
          refine le_sInf ?_
          intro y hy
          rcases hy with ⟨z, hxz, rfl⟩
          exact le_sSup ⟨(x, (upper x).toReal), hpΓ, hxz, by simp [hu]⟩
  have hΓNonempty : Γ.Nonempty := by
    by_cases hEmpty : Γ = ∅
    · let Δ : Set (ℝ × ℝ) := {(0, 0)}
      have hSubset : Γ ⊆ Δ := by
        rw [hEmpty]
        intro p hp
        simp at hp
      have hΔOrdered : IsCoordinatewiseTotallyOrdered Δ := by
        intro p hp q hq hpq
        have hp' : p = (0, 0) := by simpa [Δ] using hp
        have hq' : q = (0, 0) := by simpa [Δ] using hq
        rcases hp' with rfl
        rcases hq' with rfl
        exact False.elim (hpq rfl)
      have hEq := hmaximal hSubset hΔOrdered
      have : (0, 0) ∈ Γ := by simpa [Δ] using congrArg (fun S => (0, 0) ∈ S) hEq
      exact ⟨(0, 0), this⟩
    · exact Set.nonempty_iff_ne_empty.mpr hEmpty
  refine ⟨lower, hlowerMono, hΓNonempty, ?_⟩
  ext p
  constructor
  · intro hpΓ
    simpa [hLeftEq, hRightEq] using hmemBand_of_memΓ p hpΓ
  · intro hpBand
    have hpBand' :
        lower p.1 ≤ ((p.2 : ℝ) : EReal) ∧ ((p.2 : ℝ) : EReal) ≤ upper p.1 := by
      simpa [hLeftEq, hRightEq] using hpBand
    exact hmemΓ_of_memBand p.1 p.2 hpBand'.1 hpBand'.2

-- Proof sketch: for a monotone profile `φ`, the band
-- `{(x, xStar) | φ_-(x) ≤ xStar ≤ φ_+(x)}` is totally ordered by the product order because both
-- boundary profiles are nondecreasing. Maximality follows since adding any point outside the band
-- breaks comparability with a point on the appropriate vertical segment. Conversely, an
-- inclusion-maximal coordinatewise chain determines monotone lower and upper boundary profiles in
-- the first coordinate, and these recover the chain as a complete non-decreasing curve.
/-- Remark 5.24.3: a subset `Γ ⊆ ℝ²` is a complete non-decreasing curve if and only if it is a
maximal totally ordered subset of `ℝ²` with respect to the coordinatewise partial ordering. -/
theorem isCompleteNondecreasingCurve_iff_isMaximalCoordinatewiseTotallyOrdered
    (Γ : Set (ℝ × ℝ)) :
    IsCompleteNondecreasingCurve Γ ↔ IsMaximalCoordinatewiseTotallyOrdered Γ := by
  constructor
  · intro hΓ
    rcases hΓ with ⟨φ, hmono, hΓnonempty, hΓdef⟩
    by_cases hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)
    · rcases
        helperForRemark_5_24_3_band_eq_verticalLine_of_no_finiteWitness
          Γ φ hmono hNoFinite hΓnonempty hΓdef with
          ⟨a, hLine⟩
      simpa [hLine] using
        helperForRemark_5_24_3_verticalLine_isMaximalCoordinatewiseTotallyOrdered a
    · refine ⟨?_, ?_⟩
      · simpa [hΓdef] using helperForRemark_5_24_3_band_isCoordinatewiseTotallyOrdered φ hmono
      · intro Δ hsubset hΔOrdered
        have hFiniteWitness : ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal) :=
          not_not.mp hNoFinite
        ext p
        constructor
        · intro hpΔ
          have hpBand :
              p ∈ {q : ℝ × ℝ |
                leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                  (q.2 : EReal) ≤ rightLimitProfile φ q.1} := by
            have hpLeft : leftLimitProfile φ p.1 ≤ ((p.2 : ℝ) : EReal) := by
              by_cases hleftTop : leftLimitProfile φ p.1 = (⊤ : EReal)
              · exfalso
                rcases hFiniteWitness with ⟨x0, hx0Top, hx0Bot⟩
                by_cases hFiniteHigh :
                    ∃ z : ℝ, z < p.1 ∧
                      φ z ≠ (⊤ : EReal) ∧
                      φ z ≠ (⊥ : EReal) ∧
                      ((p.2 : ℝ) : EReal) < φ z
                · rcases hFiniteHigh with ⟨z, hzx, hzTop, hzBot, hzGt⟩
                  have hqBand :
                      (z, (φ z).toReal) ∈ {q : ℝ × ℝ |
                        leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                          (q.2 : EReal) ≤ rightLimitProfile φ q.1} :=
                    helperForRemark_5_24_3_mem_band_of_finite_value φ hmono hzTop hzBot
                  have hqΓ : (z, (φ z).toReal) ∈ Γ := by
                    simpa [hΓdef] using hqBand
                  have hqΔ : (z, (φ z).toReal) ∈ Δ := hsubset hqΓ
                  have hneq : (z, (φ z).toReal) ≠ p := by
                    intro hEq
                    exact (ne_of_lt hzx) (by simpa using congrArg Prod.fst hEq)
                  have hcomp := hΔOrdered hqΔ hpΔ hneq
                  have hzGt' :
                      ((p.2 : ℝ) : EReal) < ((((φ z).toReal : ℝ) : EReal)) := by
                    simpa [EReal.coe_toReal hzTop hzBot] using hzGt
                  have hzGtReal : p.2 < (φ z).toReal := by
                    exact_mod_cast hzGt'
                  cases hcomp with
                  | inl hle =>
                      exact (not_le_of_gt hzGtReal) hle.2
                  | inr hle =>
                      exact (not_le_of_gt hzx) hle.1
                · have hp2LtTop : ((p.2 : ℝ) : EReal) < (⊤ : EReal) := by simp
                  have hltTop :
                      ((p.2 : ℝ) : EReal) < leftLimitProfile φ p.1 := by
                    simpa [hleftTop] using hp2LtTop
                  have hlt' :
                      ((p.2 : ℝ) : EReal) < sSup (φ '' Set.Iio p.1) := by
                    simpa [leftLimitProfile] using hltTop
                  rcases (lt_sSup_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
                  rcases hyMem with ⟨zTop, hzTopLt, rfl⟩
                  have hzTopEq : φ zTop = (⊤ : EReal) := by
                    by_cases hzTop : φ zTop = (⊤ : EReal)
                    · exact hzTop
                    · have hzBot : φ zTop ≠ (⊥ : EReal) := by
                        intro hzBot
                        simpa [hzBot] using hyLt
                      exfalso
                      exact hFiniteHigh ⟨zTop, hzTopLt, hzTop, hzBot, by simpa using hyLt⟩
                  let topRegion : Set ℝ := {t : ℝ | φ t = (⊤ : EReal)}
                  have hTopNonempty : topRegion.Nonempty := ⟨zTop, hzTopEq⟩
                  have hTopBddBelow : BddBelow topRegion := by
                    refine ⟨x0, ?_⟩
                    intro t ht
                    by_contra htx0
                    have htx0' : t < x0 := lt_of_not_ge htx0
                    have hle : φ t ≤ φ x0 := hmono (le_of_lt htx0')
                    have httop : φ t = (⊤ : EReal) := ht
                    have htopLe : (⊤ : EReal) ≤ φ x0 := by simpa [httop] using hle
                    exact hx0Top (top_le_iff.mp htopLe)
                  let β : ℝ := sInf topRegion
                  have hβ : β = sInf topRegion := rfl
                  have hβLt : β < p.1 := by
                    dsimp [β]
                    exact (csInf_lt_iff hTopBddBelow hTopNonempty).2 ⟨zTop, hzTopEq, hzTopLt⟩
                  have hLeftBetaLe : leftLimitProfile φ β ≤ (((p.2 + 1 : ℝ)) : EReal) := by
                    rw [leftLimitProfile]
                    refine sSup_le ?_
                    intro y hy
                    rcases hy with ⟨z, hzβ, rfl⟩
                    have hzNotTop : φ z ≠ (⊤ : EReal) := by
                      intro hzTop
                      have hβLe : β ≤ z := by
                        rw [hβ]
                        exact csInf_le hTopBddBelow (by simpa [topRegion] using hzTop)
                      exact (not_le_of_gt hzβ) hβLe
                    by_cases hzBot : φ z = (⊥ : EReal)
                    · simp [hzBot]
                    · have hp2Lt : ((p.2 : ℝ) : EReal) < (((p.2 + 1 : ℝ)) : EReal) := by
                        exact_mod_cast (show p.2 < p.2 + 1 by linarith)
                      by_contra hyBound
                      have hyGt : (((p.2 + 1 : ℝ)) : EReal) < φ z := lt_of_not_ge hyBound
                      have hzLtP : z < p.1 := lt_trans hzβ hβLt
                      have hp2LtZ : ((p.2 : ℝ) : EReal) < φ z := lt_of_lt_of_le hp2Lt (le_of_lt hyGt)
                      exact hFiniteHigh ⟨z, hzLtP, hzNotTop, hzBot, hp2LtZ⟩
                  have hRightBetaTop : rightLimitProfile φ β = (⊤ : EReal) := by
                    rw [rightLimitProfile, sInf_eq_top]
                    intro y hy
                    rcases hy with ⟨z, hzβ, rfl⟩
                    exact
                      helperForRemark_5_24_3_eq_top_of_lt_sInf_topRegion
                        φ hmono hzβ hβ hTopBddBelow hTopNonempty
                  have hqBand :
                      (β, p.2 + 1) ∈ {q : ℝ × ℝ |
                        leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                          (q.2 : EReal) ≤ rightLimitProfile φ q.1} := by
                    refine ⟨hLeftBetaLe, ?_⟩
                    simpa [hRightBetaTop]
                  have hqΓ : (β, p.2 + 1) ∈ Γ := by
                    simpa [hΓdef] using hqBand
                  have hqΔ : (β, p.2 + 1) ∈ Δ := hsubset hqΓ
                  have hneq : (β, p.2 + 1) ≠ p := by
                    intro hEq
                    exact (ne_of_lt hβLt) (by simpa using congrArg Prod.fst hEq)
                  have hcomp := hΔOrdered hqΔ hpΔ hneq
                  cases hcomp with
                  | inl hle =>
                      exact (not_le_of_gt (show p.2 < p.2 + 1 by linarith)) hle.2
                  | inr hle =>
                      exact (not_le_of_gt hβLt) hle.1
              · by_contra hLeftFail
                have hlt :
                    ((p.2 : ℝ) : EReal) < leftLimitProfile φ p.1 := lt_of_not_ge hLeftFail
                have hlt' :
                    ((p.2 : ℝ) : EReal) < sSup (φ '' Set.Iio p.1) := by
                  simpa [leftLimitProfile] using hlt
                rcases (lt_sSup_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
                rcases hyMem with ⟨z, hzx, rfl⟩
                have hzTop : φ z ≠ (⊤ : EReal) := by
                  intro hzTop
                  have htopLe : (⊤ : EReal) ≤ leftLimitProfile φ p.1 := by
                    simpa [leftLimitProfile, hzTop] using
                      (le_sSup ⟨z, hzx, rfl⟩ : φ z ≤ sSup (φ '' Set.Iio p.1))
                  exact hleftTop (top_unique htopLe)
                have hzBot : φ z ≠ (⊥ : EReal) := by
                  intro hzBot
                  simpa [hzBot] using hyLt
                have hqBand :
                    (z, (φ z).toReal) ∈ {q : ℝ × ℝ |
                      leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                        (q.2 : EReal) ≤ rightLimitProfile φ q.1} :=
                  helperForRemark_5_24_3_mem_band_of_finite_value φ hmono hzTop hzBot
                have hqΓ : (z, (φ z).toReal) ∈ Γ := by
                  simpa [hΓdef] using hqBand
                have hqΔ : (z, (φ z).toReal) ∈ Δ := hsubset hqΓ
                have hneq : (z, (φ z).toReal) ≠ p := by
                  intro hEq
                  exact (ne_of_lt hzx) (by simpa using congrArg Prod.fst hEq)
                have hcomp := hΔOrdered hqΔ hpΔ hneq
                have hyLt' :
                    ((p.2 : ℝ) : EReal) < ((((φ z).toReal : ℝ) : EReal)) := by
                  simpa [EReal.coe_toReal hzTop hzBot] using hyLt
                have hyLtReal : p.2 < (φ z).toReal := by
                  exact_mod_cast hyLt'
                cases hcomp with
                | inl hle =>
                    exact (not_le_of_gt hyLtReal) hle.2
                | inr hle =>
                    exact (not_le_of_gt hzx) hle.1
            have hpRight : ((p.2 : ℝ) : EReal) ≤ rightLimitProfile φ p.1 := by
              by_cases hrightBot : rightLimitProfile φ p.1 = (⊥ : EReal)
              · exfalso
                rcases hFiniteWitness with ⟨x0, hx0Top, hx0Bot⟩
                by_cases hFiniteLow :
                    ∃ z : ℝ, p.1 < z ∧
                      φ z ≠ (⊤ : EReal) ∧
                      φ z ≠ (⊥ : EReal) ∧
                      φ z < ((p.2 : ℝ) : EReal)
                · rcases hFiniteLow with ⟨z, hzx, hzTop, hzBot, hzLt⟩
                  have hqBand :
                      (z, (φ z).toReal) ∈ {q : ℝ × ℝ |
                        leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                          (q.2 : EReal) ≤ rightLimitProfile φ q.1} :=
                    helperForRemark_5_24_3_mem_band_of_finite_value φ hmono hzTop hzBot
                  have hqΓ : (z, (φ z).toReal) ∈ Γ := by
                    simpa [hΓdef] using hqBand
                  have hqΔ : (z, (φ z).toReal) ∈ Δ := hsubset hqΓ
                  have hneq : p ≠ (z, (φ z).toReal) := by
                    intro hEq
                    exact (ne_of_lt hzx) (by simpa using congrArg Prod.fst hEq)
                  have hcomp := hΔOrdered hpΔ hqΔ hneq
                  have hzLt' :
                      ((((φ z).toReal : ℝ) : EReal)) < ((p.2 : ℝ) : EReal) := by
                    simpa [EReal.coe_toReal hzTop hzBot] using hzLt
                  have hzLtReal : (φ z).toReal < p.2 := by
                    exact_mod_cast hzLt'
                  cases hcomp with
                  | inl hle =>
                      exact (not_le_of_gt hzLtReal) hle.2
                  | inr hle =>
                      exact (not_le_of_gt hzx) hle.1
                · have hbotLtP : (⊥ : EReal) < ((p.2 : ℝ) : EReal) := by simp
                  have hltBot :
                      rightLimitProfile φ p.1 < ((p.2 : ℝ) : EReal) := by
                    simpa [hrightBot] using hbotLtP
                  have hlt' :
                      sInf (φ '' Set.Ioi p.1) < ((p.2 : ℝ) : EReal) := by
                    simpa [rightLimitProfile] using hltBot
                  rcases (sInf_lt_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
                  rcases hyMem with ⟨zBot, hzBotGt, rfl⟩
                  have hzBotEq : φ zBot = (⊥ : EReal) := by
                    by_cases hzBot : φ zBot = (⊥ : EReal)
                    · exact hzBot
                    · have hzTop : φ zBot ≠ (⊤ : EReal) := by
                        intro hzTop
                        simpa [hzTop] using hyLt
                      exfalso
                      exact hFiniteLow ⟨zBot, hzBotGt, hzTop, hzBot, by simpa using hyLt⟩
                  let botRegion : Set ℝ := {t : ℝ | φ t = (⊥ : EReal)}
                  have hBotNonempty : botRegion.Nonempty := ⟨zBot, hzBotEq⟩
                  have hBotBddAbove : BddAbove botRegion := by
                    refine ⟨x0, ?_⟩
                    intro t ht
                    by_contra hx0t
                    have hx0t' : x0 < t := lt_of_not_ge hx0t
                    have hle : φ x0 ≤ φ t := hmono (le_of_lt hx0t')
                    have htbot : φ t = (⊥ : EReal) := ht
                    have hx0LeBot : φ x0 ≤ (⊥ : EReal) := by simpa [htbot] using hle
                    exact hx0Bot (le_bot_iff.mp hx0LeBot)
                  let α : ℝ := sSup botRegion
                  have hα : α = sSup botRegion := rfl
                  have hpLtα : p.1 < α := by
                    dsimp [α]
                    exact (lt_csSup_iff hBotBddAbove hBotNonempty).2 ⟨zBot, hzBotEq, hzBotGt⟩
                  have hLeftAlphaBot : leftLimitProfile φ α = (⊥ : EReal) := by
                    rw [leftLimitProfile, sSup_eq_bot]
                    intro y hy
                    rcases hy with ⟨z, hzα, rfl⟩
                    exact
                      helperForRemark_5_24_3_eq_bot_of_lt_sSup_botRegion
                        φ hmono hzα hα hBotBddAbove hBotNonempty
                  have hRightAlphaGe :
                      (((p.2 - 1 : ℝ)) : EReal) ≤ rightLimitProfile φ α := by
                    rw [rightLimitProfile]
                    refine le_sInf ?_
                    intro y hy
                    rcases hy with ⟨z, hαz, rfl⟩
                    by_cases hzTop : φ z = (⊤ : EReal)
                    · simpa [hzTop]
                    · by_cases hzBot : φ z = (⊥ : EReal)
                      · exfalso
                        have hzLe : z ≤ α := by
                          rw [hα]
                          exact le_csSup hBotBddAbove (by simpa [botRegion] using hzBot)
                        exact (not_le_of_gt hαz) hzLe
                      · have hp2m1Le : (((p.2 - 1 : ℝ)) : EReal) ≤ φ z := by
                          by_contra hzLt
                          have hzSmall : φ z < (((p.2 - 1 : ℝ)) : EReal) := lt_of_not_ge hzLt
                          have hp2m1LtP2 : (((p.2 - 1 : ℝ)) : EReal) < ((p.2 : ℝ) : EReal) := by
                            exact_mod_cast (show p.2 - 1 < p.2 by linarith)
                          have hzLtP2 : φ z < ((p.2 : ℝ) : EReal) :=
                            lt_of_lt_of_le hzSmall (le_of_lt hp2m1LtP2)
                          have hpLtZ : p.1 < z := lt_trans hpLtα hαz
                          exact hFiniteLow ⟨z, hpLtZ, hzTop, hzBot, hzLtP2⟩
                        exact hp2m1Le
                  have hqBand :
                      (α, p.2 - 1) ∈ {q : ℝ × ℝ |
                        leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                          (q.2 : EReal) ≤ rightLimitProfile φ q.1} := by
                    refine ⟨?_, hRightAlphaGe⟩
                    simpa [hLeftAlphaBot]
                  have hqΓ : (α, p.2 - 1) ∈ Γ := by
                    simpa [hΓdef] using hqBand
                  have hqΔ : (α, p.2 - 1) ∈ Δ := hsubset hqΓ
                  have hneq : p ≠ (α, p.2 - 1) := by
                    intro hEq
                    exact (ne_of_lt hpLtα) (by simpa using congrArg Prod.fst hEq)
                  have hcomp := hΔOrdered hpΔ hqΔ hneq
                  cases hcomp with
                  | inl hle =>
                      exact (not_le_of_gt (show p.2 - 1 < p.2 by linarith)) hle.2
                  | inr hle =>
                      exact (not_le_of_gt hpLtα) hle.1
              · by_contra hRightFail
                have hlt :
                    rightLimitProfile φ p.1 < ((p.2 : ℝ) : EReal) := lt_of_not_ge hRightFail
                have hlt' :
                    sInf (φ '' Set.Ioi p.1) < ((p.2 : ℝ) : EReal) := by
                  simpa [rightLimitProfile] using hlt
                rcases (sInf_lt_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
                rcases hyMem with ⟨z, hzx, rfl⟩
                have hzBot : φ z ≠ (⊥ : EReal) := by
                  intro hzBot
                  have hbotLe : rightLimitProfile φ p.1 ≤ (⊥ : EReal) := by
                    simpa [rightLimitProfile, hzBot] using
                      (sInf_le ⟨z, hzx, rfl⟩ : sInf (φ '' Set.Ioi p.1) ≤ φ z)
                  exact hrightBot (bot_unique hbotLe)
                have hzTop : φ z ≠ (⊤ : EReal) := by
                  intro hzTop
                  simpa [hzTop] using hyLt
                have hqBand :
                    (z, (φ z).toReal) ∈ {q : ℝ × ℝ |
                      leftLimitProfile φ q.1 ≤ (q.2 : EReal) ∧
                        (q.2 : EReal) ≤ rightLimitProfile φ q.1} :=
                  helperForRemark_5_24_3_mem_band_of_finite_value φ hmono hzTop hzBot
                have hqΓ : (z, (φ z).toReal) ∈ Γ := by
                  simpa [hΓdef] using hqBand
                have hqΔ : (z, (φ z).toReal) ∈ Δ := hsubset hqΓ
                have hneq : p ≠ (z, (φ z).toReal) := by
                  intro hEq
                  exact (ne_of_lt hzx) (by simpa using congrArg Prod.fst hEq)
                have hcomp := hΔOrdered hpΔ hqΔ hneq
                have hyLt' :
                    ((((φ z).toReal : ℝ) : EReal)) < ((p.2 : ℝ) : EReal) := by
                  simpa [EReal.coe_toReal hzTop hzBot] using hyLt
                have hyLtReal : (φ z).toReal < p.2 := by
                  exact_mod_cast hyLt'
                cases hcomp with
                | inl hle =>
                    exact (not_le_of_gt hyLtReal) hle.2
                | inr hle =>
                    exact (not_le_of_gt hzx) hle.1
            exact ⟨hpLeft, hpRight⟩
          simpa [hΓdef] using hpBand
        · intro hpΓ
          exact hsubset hpΓ
  · intro hΓMax
    exact helperForRemark_5_24_3_completeCurve_of_maximalCoordinatewiseTotallyOrdered Γ hΓMax

/-- The sum-coordinate parameter map `T(x, xStar) = x + xStar` on a subset of `ℝ²`. -/
def completeNondecreasingCurveSumMap (Γ : Set (ℝ × ℝ)) : Γ → ℝ :=
  fun p => p.1.1 + p.1.2

/-- On a coordinatewise ordered pair, equality of the sum coordinate forces equality of the
point. -/
lemma helperForRemark_5_24_3_eq_of_le_and_sumEq
    {p q : ℝ × ℝ} (hpq : p ≤ q) (hsum : p.1 + p.2 = q.1 + q.2) :
    p = q := by
  have hx : p.1 = q.1 := by
    linarith [hpq.1, hpq.2]
  have hy : p.2 = q.2 := by
    linarith [hpq.1, hpq.2]
  exact Prod.ext hx hy

/-- The sum map is injective on any coordinatewise totally ordered subset of `ℝ²`. -/
lemma helperForRemark_5_24_3_sumMap_injective
    {Γ : Set (ℝ × ℝ)} (hordered : IsCoordinatewiseTotallyOrdered Γ) :
    Function.Injective (completeNondecreasingCurveSumMap Γ) := by
  intro p q hpqSum
  by_cases hpqEq : (p : ℝ × ℝ) = q
  · exact Subtype.ext hpqEq
  · have hcomp : (p : ℝ × ℝ) ≤ q ∨ q ≤ (p : ℝ × ℝ) :=
      hordered p.property q.property hpqEq
    cases hcomp with
    | inl hpqLe =>
        exact Subtype.ext (helperForRemark_5_24_3_eq_of_le_and_sumEq hpqLe hpqSum)
    | inr hqpLe =>
        exact Subtype.ext (helperForRemark_5_24_3_eq_of_le_and_sumEq hqpLe hpqSum.symm).symm

/-- The sum map on a subtype of `ℝ²` is continuous. -/
lemma helperForRemark_5_24_3_sumMap_continuous
    (Γ : Set (ℝ × ℝ)) :
    Continuous (completeNondecreasingCurveSumMap Γ) := by
  change Continuous fun p : Γ => Prod.fst p.1 + Prod.snd p.1
  exact continuous_subtype_val.fst.add continuous_subtype_val.snd

/-- Along a coordinatewise chain, if two points have nearly equal sums, then both coordinates are
nearly equal as well. This is the local rigidity behind continuity of the inverse sum map. -/
lemma helperForRemark_5_24_3_abs_coordDiff_lt_of_abs_sumDiff_lt
    {Γ : Set (ℝ × ℝ)} (hordered : IsCoordinatewiseTotallyOrdered Γ)
    {p q : Γ} {ε : ℝ}
    (hε : |completeNondecreasingCurveSumMap Γ q - completeNondecreasingCurveSumMap Γ p| < ε) :
    |q.1.1 - p.1.1| < ε ∧ |q.1.2 - p.1.2| < ε := by
  by_cases hpq : p = q
  · subst hpq
    constructor <;> simpa using hε
  · have hcomp := hordered p.2 q.2 (by
        intro hpq'
        apply hpq
        exact Subtype.ext hpq')
    cases hcomp with
    | inl hpqLe =>
        have hxNonneg : 0 ≤ q.1.1 - p.1.1 := sub_nonneg.mpr hpqLe.1
        have hyNonneg : 0 ≤ q.1.2 - p.1.2 := sub_nonneg.mpr hpqLe.2
        have hsum :
            completeNondecreasingCurveSumMap Γ q -
                completeNondecreasingCurveSumMap Γ p =
              (q.1.1 - p.1.1) + (q.1.2 - p.1.2) := by
          simp [completeNondecreasingCurveSumMap]
          ring
        have hsumAbs :
            |(q.1.1 - p.1.1) + (q.1.2 - p.1.2)| < ε := by
          simpa [hsum] using hε
        have hsumLt : (q.1.1 - p.1.1) + (q.1.2 - p.1.2) < ε := by
          simpa [abs_of_nonneg (add_nonneg hxNonneg hyNonneg)] using hsumAbs
        constructor
        · have hxLe :
              q.1.1 - p.1.1 ≤ (q.1.1 - p.1.1) + (q.1.2 - p.1.2) := by linarith
          have hxLt : q.1.1 - p.1.1 < ε := lt_of_le_of_lt hxLe hsumLt
          simpa [abs_of_nonneg hxNonneg] using hxLt
        · have hyLe :
              q.1.2 - p.1.2 ≤ (q.1.1 - p.1.1) + (q.1.2 - p.1.2) := by linarith
          have hyLt : q.1.2 - p.1.2 < ε := lt_of_le_of_lt hyLe hsumLt
          simpa [abs_of_nonneg hyNonneg] using hyLt
    | inr hqpLe =>
        have hxNonneg : 0 ≤ p.1.1 - q.1.1 := sub_nonneg.mpr hqpLe.1
        have hyNonneg : 0 ≤ p.1.2 - q.1.2 := sub_nonneg.mpr hqpLe.2
        have hsum :
            completeNondecreasingCurveSumMap Γ p -
                completeNondecreasingCurveSumMap Γ q =
              (p.1.1 - q.1.1) + (p.1.2 - q.1.2) := by
          simp [completeNondecreasingCurveSumMap]
          ring
        have hsumAbs :
            |(p.1.1 - q.1.1) + (p.1.2 - q.1.2)| < ε := by
          have := hε
          simpa [abs_sub_comm, hsum] using this
        have hsumLt : (p.1.1 - q.1.1) + (p.1.2 - q.1.2) < ε := by
          simpa [abs_of_nonneg (add_nonneg hxNonneg hyNonneg)] using hsumAbs
        constructor
        · have hxLe :
              p.1.1 - q.1.1 ≤ (p.1.1 - q.1.1) + (p.1.2 - q.1.2) := by linarith
          have hxLt : p.1.1 - q.1.1 < ε := lt_of_le_of_lt hxLe hsumLt
          simpa [abs_of_nonneg hxNonneg, abs_sub_comm] using hxLt
        · have hyLe :
              p.1.2 - q.1.2 ≤ (p.1.1 - q.1.1) + (p.1.2 - q.1.2) := by linarith
          have hyLt : p.1.2 - q.1.2 < ε := lt_of_le_of_lt hyLe hsumLt
          simpa [abs_of_nonneg hyNonneg, abs_sub_comm] using hyLt

/-- The first-coordinate projection `I = {x | ∃ xStar, (x, xStar) ∈ Γ}` of a curve `Γ ⊆ ℝ²`. -/
def completeNondecreasingCurveProjection (Γ : Set (ℝ × ℝ)) : Set ℝ :=
  {x | ∃ xStar : ℝ, (x, xStar) ∈ Γ}

/-- A graph-like description of a subset `Γ ⊆ ℝ²` over its first-coordinate projection, allowing
vertical segments through the gap between monotone one-sided boundary profiles and horizontal
segments coming from flat portions of those profiles. -/
def GraphLikeWithVerticalHorizontalSegments (Γ : Set (ℝ × ℝ)) : Prop :=
  ∃ I : Set ℝ,
    I = completeNondecreasingCurveProjection Γ ∧
      ∃ φ : ℝ → EReal,
        Monotone φ ∧
          Γ.Nonempty ∧
          Γ = {p : ℝ × ℝ |
            p.1 ∈ I ∧
              leftLimitProfile φ p.1 ≤ (p.2 : EReal) ∧
                (p.2 : EReal) ≤ rightLimitProfile φ p.1}

/-- On a vertical line over `a`, the sum map is the obvious affine homeomorphism to `ℝ`. -/
lemma helperForRemark_5_24_3_verticalLine_sumMap_homeomorph
    (a : ℝ) :
    ∃ e : {p : ℝ × ℝ | p.1 = a} ≃ₜ ℝ,
      ∀ p : {p : ℝ × ℝ | p.1 = a},
        e p = completeNondecreasingCurveSumMap {p : ℝ × ℝ | p.1 = a} p := by
  refine ⟨{ toEquiv := { toFun := fun p => p.1.1 + p.1.2
                         invFun := fun r => ⟨(a, r - a), by simp⟩
                         left_inv := ?_
                         right_inv := ?_ }
            continuous_toFun := by
              change Continuous fun p : {p : ℝ × ℝ | p.1 = a} => Prod.fst p.1 + Prod.snd p.1
              exact continuous_subtype_val.fst.add continuous_subtype_val.snd
            continuous_invFun := by
              exact (continuous_const.prodMk (continuous_id.sub continuous_const)).subtype_mk
                (by intro r; simp)
          }, ?_⟩
  · rintro ⟨⟨x, y⟩, hx⟩
    apply Subtype.ext
    have hx' : x = a := by simpa using hx
    ext <;> simp [hx'] <;> linarith
  · intro r
    simp
  · intro p
    rfl

-- Proof sketch: write `Γ` as the band between the left and right limit profiles of a monotone
-- extended-real function `φ` from Definition 5.24.4. Those one-sided profiles encode the
-- graph-like geometry over the projected set of first coordinates, with vertical segments at jump
-- points and horizontal segments on flat portions. The same monotone profile description then
-- shows that the sum map is strictly increasing along the curve, hence bijective onto `ℝ`;
-- continuity and continuity of the inverse follow from the profile representation.
/-- Proposition 5.24.1: if `Γ` is a complete non-decreasing curve in `ℝ²`, then it is
graph-like with possible horizontal and vertical segments, and the map
`T(x, xStar) = x + xStar` identifies `Γ` homeomorphically with `ℝ`. -/
theorem completeNondecreasingCurve_sumMap_homeomorph
    {Γ : Set (ℝ × ℝ)} (hΓ : IsCompleteNondecreasingCurve Γ) :
    GraphLikeWithVerticalHorizontalSegments Γ ∧
      ∃ e : Γ ≃ₜ ℝ,
        ∀ p : Γ, e p = completeNondecreasingCurveSumMap Γ p := by
  have hΓcurve : IsCompleteNondecreasingCurve Γ := hΓ
  rcases hΓ with ⟨φ, hmono, hΓnonempty, hΓdef⟩
  refine ⟨?_, ?_⟩
  · refine ⟨completeNondecreasingCurveProjection Γ, rfl, φ, hmono, hΓnonempty, ?_⟩
    ext p
    constructor
    · intro hpΓ
      refine ⟨?_, ?_⟩
      · exact ⟨p.2, hpΓ⟩
      · simpa [hΓdef] using hpΓ
    · intro hp
      exact (by simpa [hΓdef] using hp.2 : p ∈ Γ)
  · have hΓMax :
        IsMaximalCoordinatewiseTotallyOrdered Γ :=
      (isCompleteNondecreasingCurve_iff_isMaximalCoordinatewiseTotallyOrdered Γ).1 hΓcurve
    have hordered : IsCoordinatewiseTotallyOrdered Γ := hΓMax.1
    have hContinuous :
        Continuous (completeNondecreasingCurveSumMap Γ) :=
      helperForRemark_5_24_3_sumMap_continuous Γ
    have hInjective :
        Function.Injective (completeNondecreasingCurveSumMap Γ) :=
      helperForRemark_5_24_3_sumMap_injective hordered
    by_cases hNoFinite : ¬ ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)
    · rcases
        helperForRemark_5_24_3_band_eq_verticalLine_of_no_finiteWitness
          Γ φ hmono hNoFinite hΓnonempty hΓdef with
        ⟨a, hLine⟩
      rcases helperForRemark_5_24_3_verticalLine_sumMap_homeomorph a with ⟨eLine, heLine⟩
      refine ⟨(Homeomorph.setCongr hLine).trans eLine, ?_⟩
      intro p
      change eLine ((Homeomorph.setCongr hLine) p) = completeNondecreasingCurveSumMap Γ p
      simpa [completeNondecreasingCurveSumMap, hLine] using
        heLine ((Homeomorph.setCongr hLine) p)
    · -- Remaining nondegenerate branch: use a finite witness of `φ`, analyze the ordered
      -- graph/band structure, and show the sum map has a continuous inverse given by the unique
      -- intersection with each diagonal.
      have hFiniteWitness : ∃ x : ℝ, φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal) :=
        not_not.mp hNoFinite
      rcases hFiniteWitness with ⟨x0, hx0Top, hx0Bot⟩
      let c : ℝ := (φ x0).toReal
      have hc : ((c : ℝ) : EReal) = φ x0 := by
        simp [c, EReal.coe_toReal hx0Top hx0Bot]
      have hLeftFiniteUpper :
          ∀ x : ℝ, x < x0 → leftLimitProfile φ x ≤ ((c : ℝ) : EReal) := by
        intro x hxx0
        refine sSup_le ?_
        intro y hy
        rcases hy with ⟨z, hzx, rfl⟩
        have hzle : z ≤ x0 := le_trans (le_of_lt hzx) (le_of_lt hxx0)
        exact le_trans (hmono hzle) (by simpa [hc])
      have hRightFiniteLower :
          ∀ x : ℝ, x0 < x → ((c : ℝ) : EReal) ≤ rightLimitProfile φ x := by
        intro x hx0x
        refine le_sInf ?_
        intro y hy
        rcases hy with ⟨z, hxz, rfl⟩
        have hx0z : x0 ≤ z := le_trans (le_of_lt hx0x) (le_of_lt hxz)
        exact by simpa [hc] using hmono hx0z
      have hLeftFiniteLower :
          ∀ x : ℝ, x0 < x → ((c : ℝ) : EReal) ≤ leftLimitProfile φ x := by
        intro x hx0x
        refine le_sSup ?_
        exact ⟨x0, hx0x, by simpa [hc]⟩
      let L : ℝ → EReal := fun x => ((x : ℝ) : EReal) + leftLimitProfile φ x
      let U : ℝ → EReal := fun x => ((x : ℝ) : EReal) + rightLimitProfile φ x
      have hLLeU : ∀ x : ℝ, L x ≤ U x := by
        intro x
        simpa [L, U] using add_le_add_right
          ((helperForRemark_5_24_3_leftLimitProfile_le_value_le_rightLimitProfile φ hmono x).1.trans
            (helperForRemark_5_24_3_leftLimitProfile_le_value_le_rightLimitProfile φ hmono x).2)
          (((x : ℝ) : EReal))
      have hLNonempty :
          ∀ r : ℝ, ({x : ℝ | L x ≤ ((r : ℝ) : EReal)} : Set ℝ).Nonempty := by
        intro r
        let x : ℝ := min (x0 - 1) (r - c - 1)
        have hxx0 : x < x0 := by
          dsimp [x]
          have hxle : x ≤ x0 - 1 := min_le_left _ _
          linarith
        refine ⟨x, ?_⟩
        have hleft : leftLimitProfile φ x ≤ ((c : ℝ) : EReal) := hLeftFiniteUpper x hxx0
        have hxc : (((x + c : ℝ)) : EReal) ≤ ((r : ℝ) : EReal) := by
          exact_mod_cast (show x + c ≤ r by
            dsimp [x]
            have hxle : x ≤ r - c - 1 := by exact min_le_right _ _
            linarith)
        calc
          L x = ((x : ℝ) : EReal) + leftLimitProfile φ x := rfl
          _ ≤ ((x : ℝ) : EReal) + ((c : ℝ) : EReal) := by
            simpa using add_le_add_right hleft (((x : ℝ) : EReal))
          _ = (((x + c : ℝ)) : EReal) := by simp
          _ ≤ ((r : ℝ) : EReal) := hxc
      have hLBounded :
          ∀ r : ℝ, BddAbove ({x : ℝ | L x ≤ ((r : ℝ) : EReal)} : Set ℝ) := by
        intro r
        refine ⟨max x0 (r - c + 1), ?_⟩
        intro x hx
        by_contra hgt
        have hxLarge : max x0 (r - c + 1) < x := lt_of_not_ge hgt
        have hx0x : x0 < x := lt_of_le_of_lt (le_max_left _ _) hxLarge
        have hright : ((c : ℝ) : EReal) ≤ rightLimitProfile φ x := hRightFiniteLower x hx0x
        have hLc : ((r : ℝ) : EReal) < L x := by
          have hxc : ((r : ℝ) : EReal) < ((x + c : ℝ) : EReal) := by
            exact_mod_cast (show r < x + c by
              have hxge : r - c + 1 ≤ x := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hxLarge)
              linarith)
          have hLc' :
              (((x + c : ℝ)) : EReal) ≤ L x := by
            calc
              (((x + c : ℝ)) : EReal) = ((x : ℝ) : EReal) + ((c : ℝ) : EReal) := by simp
              _ ≤ ((x : ℝ) : EReal) + leftLimitProfile φ x := by
                simpa using add_le_add_right (hLeftFiniteLower x hx0x) (((x : ℝ) : EReal))
          exact lt_of_lt_of_le hxc hLc'
        exact (not_lt_of_ge hx) hLc
      have hExistsOnDiagonal :
          ∀ r : ℝ, ∃ p : Γ, completeNondecreasingCurveSumMap Γ p = r := by
        intro r
        let A : Set ℝ := {x : ℝ | L x ≤ ((r : ℝ) : EReal)}
        have hA_nonempty : A.Nonempty := by
          simpa [A] using hLNonempty r
        have hA_bdd : BddAbove A := by
          simpa [A] using hLBounded r
        let ξ : ℝ := sSup A
        have hξ_upper : ∀ a ∈ A, a ≤ ξ := by
          intro a ha
          exact le_csSup hA_bdd ha
        have hξ_lub : IsLUB A ξ := isLUB_csSup hA_nonempty hA_bdd
        have hBandAtξ :
            leftLimitProfile φ ξ ≤ (((r - ξ : ℝ) : ℝ) : EReal) ∧
              ((((r - ξ : ℝ) : ℝ) : EReal) ≤ rightLimitProfile φ ξ) := by
          constructor
          · by_contra hleftFail
            have hleftFail' : (((r - ξ : ℝ) : ℝ) : EReal) < leftLimitProfile φ ξ := by
              exact lt_of_not_ge hleftFail
            have hlt' :
                (((r - ξ : ℝ) : ℝ) : EReal) < sSup (φ '' Set.Iio ξ) := by
              simpa [leftLimitProfile] using hleftFail'
            rcases (lt_sSup_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
            rcases hyMem with ⟨z, hzξ, rfl⟩
            obtain ⟨c', hc'low, hc'high⟩ := EReal.lt_iff_exists_real_btwn.1 hyLt
            let w : ℝ := max z (r - c')
            have hwlt : w < ξ := by
              dsimp [w]
              have hzlt : z < ξ := hzξ
              have hrc' : r - c' < ξ := by
                exact_mod_cast (show r - c' < ξ by
                  have : r - ξ < c' := by exact_mod_cast hc'low
                  linarith)
              exact max_lt hzlt hrc'
            have hwUpper : ∀ a ∈ A, a ≤ w := by
              intro a haA
              by_contra haw
              have hza : z < a := lt_of_le_of_lt (le_max_left _ _) (lt_of_not_ge haw)
              have hrca : r - c' < a := lt_of_le_of_lt (le_max_right _ _) (lt_of_not_ge haw)
              have hc'Left : ((c' : ℝ) : EReal) < leftLimitProfile φ a := by
                have hzmem : (φ z) ≤ leftLimitProfile φ a := by
                  exact le_sSup ⟨z, hza, rfl⟩
                exact lt_of_lt_of_le hc'high hzmem
              have hLa : ((r : ℝ) : EReal) < L a := by
                have hrca' : ((r : ℝ) : EReal) < (((a + c' : ℝ)) : EReal) := by
                  exact_mod_cast (show r < a + c' by linarith)
                have hsum' :
                    (((a + c' : ℝ)) : EReal) < L a := by
                  calc
                    (((a + c' : ℝ)) : EReal) = ((a : ℝ) : EReal) + ((c' : ℝ) : EReal) := by simp
                    _ < ((a : ℝ) : EReal) + leftLimitProfile φ a := by
                      simpa [L] using EReal.add_lt_add_left_coe hc'Left a
                exact lt_trans hrca' hsum'
              exact (not_lt_of_ge haA) hLa
            have : ξ ≤ w := hξ_lub.2 hwUpper
            exact (not_le_of_gt hwlt) this
          · by_contra hrightFail
            have hrightFail' : rightLimitProfile φ ξ < (((r - ξ : ℝ) : ℝ) : EReal) := by
              exact lt_of_not_ge hrightFail
            have hlt' :
                sInf (φ '' Set.Ioi ξ) < (((r - ξ : ℝ) : ℝ) : EReal) := by
              simpa [rightLimitProfile] using hrightFail'
            rcases (sInf_lt_iff).1 hlt' with ⟨y, hyMem, hyLt⟩
            rcases hyMem with ⟨z, hξz, rfl⟩
            obtain ⟨c', hc'low, hc'high⟩ := EReal.lt_iff_exists_real_btwn.1 hyLt
            let w : ℝ := min z (r - c')
            have hξltw : ξ < w := by
              dsimp [w]
              have hrc' : ξ < r - c' := by
                exact_mod_cast (show ξ < r - c' by
                  have : c' < r - ξ := by exact_mod_cast hc'high
                  linarith)
              exact lt_min hξz hrc'
            let a : ℝ := (ξ + w) / 2
            have hξa : ξ < a := by
              dsimp [a]
              linarith [hξltw]
            have haw : a < w := by
              dsimp [a]
              linarith [hξltw]
            have haz : a < z := lt_of_lt_of_le haw (min_le_left _ _)
            have harc : a < r - c' := lt_of_lt_of_le haw (min_le_right _ _)
            have hUa : U a < ((r : ℝ) : EReal) := by
              have hrightA : rightLimitProfile φ a ≤ φ z := by
                exact sInf_le ⟨z, haz, rfl⟩
              have hsum1 : U a ≤ ((a : ℝ) : EReal) + φ z := by
                simpa [U] using add_le_add_right hrightA (((a : ℝ) : EReal))
              have hsum2 : ((a : ℝ) : EReal) + φ z < ((a : ℝ) : EReal) + ((c' : ℝ) : EReal) := by
                simpa using EReal.add_lt_add_left_coe hc'low a
              have hsum3 : ((a : ℝ) : EReal) + ((c' : ℝ) : EReal) < ((r : ℝ) : EReal) := by
                simpa using (show (((a + c' : ℝ)) : EReal) < ((r : ℝ) : EReal) by
                  exact_mod_cast (show a + c' < r by linarith))
              exact lt_of_le_of_lt hsum1 (lt_trans hsum2 hsum3)
            have haA : a ∈ A := by
              exact le_trans (hLLeU a) (le_of_lt hUa)
            have : a ≤ ξ := hξ_upper a haA
            exact (not_le_of_gt hξa) this
        have hpΓ : (ξ, r - ξ) ∈ Γ := by
          simpa [hΓdef] using hBandAtξ
        refine ⟨⟨(ξ, r - ξ), hpΓ⟩, ?_⟩
        simp [completeNondecreasingCurveSumMap]
      have hSurjective :
          Function.Surjective (completeNondecreasingCurveSumMap Γ) := by
        intro r
        exact hExistsOnDiagonal r
      let eEquiv : Γ ≃ ℝ :=
        Equiv.ofBijective (completeNondecreasingCurveSumMap Γ) ⟨hInjective, hSurjective⟩
      have hInvContinuousProd :
          Continuous fun r : ℝ => ((eEquiv.symm r : Γ) : ℝ × ℝ) := by
        rw [continuous_iff_continuousAt]
        intro r
        apply Metric.continuousAt_iff'.2
        intro ε hε
        filter_upwards [Metric.ball_mem_nhds r hε] with r' hr'
        have hsumAbs :
            |completeNondecreasingCurveSumMap Γ (eEquiv.symm r') -
                completeNondecreasingCurveSumMap Γ (eEquiv.symm r)| < ε := by
          have hr'' : |r' - r| < ε := by
            simpa [Metric.mem_ball, Real.dist_eq] using hr'
          change |eEquiv (eEquiv.symm r') - eEquiv (eEquiv.symm r)| < ε
          rw [eEquiv.apply_symm_apply, eEquiv.apply_symm_apply]
          exact hr''
        rcases
            helperForRemark_5_24_3_abs_coordDiff_lt_of_abs_sumDiff_lt hordered hsumAbs with
          ⟨hx, hy⟩
        rw [Prod.dist_eq]
        exact max_lt_iff.mpr ⟨by simpa [Real.dist_eq] using hx, by simpa [Real.dist_eq] using hy⟩
      have hInvContinuous : Continuous eEquiv.symm := by
        exact Continuous.subtype_mk hInvContinuousProd fun r => (eEquiv.symm r).2
      refine ⟨{ toEquiv := eEquiv
                continuous_toFun := by simpa [eEquiv] using hContinuous
                continuous_invFun := hInvContinuous }, ?_⟩
      intro p
      rfl

/-- The scalar interval-integral primitive `x ↦ ∫_a^x φ(t) dt`, recorded as an `EReal`-valued
function on `ℝ`. -/
noncomputable def oneDimensionalIntervalIntegralPrimitiveValue (φ : ℝ → EReal) (a : ℝ) :
    ℝ → EReal :=
  fun x =>
    if _hFiniteOpen : ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) then
      if _hInt : IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x then
        (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal)
      else
        (⊤ : EReal)
    else
      (⊤ : EReal)

/-- The interval-integral primitive on `ℝ`, viewed as a function on `Fin 1 → ℝ` via the unique
coordinate. -/
noncomputable def oneDimensionalIntervalIntegralPrimitive (φ : ℝ → EReal) (a : ℝ) :
    (Fin 1 → ℝ) → EReal :=
  fun x => oneDimensionalIntervalIntegralPrimitiveValue φ a (x 0)

/-- Helper for Theorem 5.24.4: evaluating the lifted primitive at a scalar point simply unwraps
the unique `Fin 1` coordinate. -/
lemma helperForTheorem_5_24_4_scalarPoint_primitive_eval
    (φ : ℝ → EReal) (a x : ℝ) :
    oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint x) =
      oneDimensionalIntervalIntegralPrimitiveValue φ a x := by
  -- The lifted primitive only reads the sole coordinate of the scalar point.
  rfl

/-- Helper for Theorem 5.24.4: the scalar interval-integral primitive is normalized at its base
point. -/
lemma helperForTheorem_5_24_4_primitiveValue_at_base
    (φ : ℝ → EReal) (a : ℝ) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a a = 0 := by
  -- The open interval between identical endpoints is empty, and the interval integral over a
  -- degenerate interval vanishes.
  simp [oneDimensionalIntervalIntegralPrimitiveValue]

/-- Helper for Theorem 5.24.4: the lifted primitive also vanishes at the scalar base point. -/
lemma helperForTheorem_5_24_4_primitive_at_scalarBasePoint
    (φ : ℝ → EReal) (a : ℝ) :
    oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) = 0 := by
  -- Reduce to the scalar normalization and then unwrap the `Fin 1` wrapper.
  simpa using
    (helperForTheorem_5_24_4_scalarPoint_primitive_eval φ a a).trans
      (helperForTheorem_5_24_4_primitiveValue_at_base φ a)

/-- Helper for Theorem 5.24.4: the scalar interval-integral primitive never takes the value
`-∞`. -/
lemma helperForTheorem_5_24_4_primitiveValue_ne_bot
    (φ : ℝ → EReal) (a x : ℝ) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊥ : EReal) := by
  dsimp [oneDimensionalIntervalIntegralPrimitiveValue]
  split_ifs <;> simp

/-- Helper for Theorem 5.24.4: the lifted interval-integral primitive also never takes the value
`-∞`. -/
lemma helperForTheorem_5_24_4_primitive_ne_bot
    (φ : ℝ → EReal) (a : ℝ) (x : Fin 1 → ℝ) :
    oneDimensionalIntervalIntegralPrimitive φ a x ≠ (⊥ : EReal) := by
  dsimp [oneDimensionalIntervalIntegralPrimitive, oneDimensionalIntervalIntegralPrimitiveValue]
  split_ifs <;> simp

/-- The scalar base point always belongs to the effective domain of the interval-integral
primitive because the primitive is normalized there. -/
lemma helperForTheorem_5_24_4_scalarBasePoint_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a : ℝ) :
    a ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a) := by
  have haEval :
      oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) = (0 : EReal) := by
    simpa using helperForTheorem_5_24_4_primitive_at_scalarBasePoint φ a
  have haNotTop :
      oneDimensionalIntervalIntegralPrimitive φ a (scalarPoint a) ≠ (⊤ : EReal) := by
    rw [haEval]
    simp
  simpa [scalarEffectiveDomain, effectiveDomain_eq, lt_top_iff_ne_top, haNotTop]

/-- Helper for Theorem 5.24.4: once convexity of the interval-integral primitive is established,
properness is automatic because the base point lies in the epigraph and the primitive never
attains `-∞`. -/
lemma helperForTheorem_5_24_4_intervalIntegralPrimitive_proper_of_convex
    (φ : ℝ → EReal) (a : ℝ)
    (hconv : ConvexFunction (oneDimensionalIntervalIntegralPrimitive φ a)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (oneDimensionalIntervalIntegralPrimitive φ a) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [ConvexFunction] using hconv
  · refine ⟨(scalarPoint a, 0), ?_⟩
    constructor
    · change scalarPoint a ∈ (Set.univ : Set (Fin 1 → ℝ))
      trivial
    · simp [helperForTheorem_5_24_4_primitive_at_scalarBasePoint φ a]
  · intro x hx
    exact helperForTheorem_5_24_4_primitive_ne_bot φ a x

/-- Helper for Theorem 5.24.4: closedness of the interval-integral primitive already gives the
properness package needed later. -/
lemma helperForTheorem_5_24_4_intervalIntegralPrimitive_proper_of_closed
    (φ : ℝ → EReal) (a : ℝ)
    (hclosed : ClosedConvexFunction (oneDimensionalIntervalIntegralPrimitive φ a)) :
    ProperConvexFunctionOn (Set.univ : Set (Fin 1 → ℝ))
      (oneDimensionalIntervalIntegralPrimitive φ a) :=
  helperForTheorem_5_24_4_intervalIntegralPrimitive_proper_of_convex φ a hclosed.1

/-- The scalar points where the monotone profile `φ` takes a genuine real value. -/
def oneDimensionalPrimitiveFiniteValueSet (φ : ℝ → EReal) : Set ℝ :=
  {x : ℝ | φ x ≠ (⊤ : EReal) ∧ φ x ≠ (⊥ : EReal)}

/-- For a monotone profile, every point between two finite-valued points is again finite-valued. -/
lemma helperForTheorem_5_24_4_finiteValueSet_mem_between
    (φ : ℝ → EReal) (hmono : Monotone φ) {x y z : ℝ}
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hz : z ∈ Set.uIcc x y) :
    z ∈ oneDimensionalPrimitiveFiniteValueSet φ := by
  rcases hx with ⟨hxTop, hxBot⟩
  rcases hy with ⟨hyTop, hyBot⟩
  by_cases hxy : x ≤ y
  · have hzIcc : z ∈ Set.Icc x y := by
      simpa [Set.uIcc_of_le hxy] using hz
    have hxz : φ x ≤ φ z := hmono hzIcc.1
    have hzy : φ z ≤ φ y := hmono hzIcc.2
    constructor
    · intro hzTop
      exact hyTop (top_le_iff.mp (hzTop ▸ hzy))
    · intro hzBot
      exact hxBot (le_bot_iff.mp (hzBot ▸ hxz))
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hzIcc : z ∈ Set.Icc y x := by
      simpa [Set.uIcc_of_ge hyx] using hz
    have hyz : φ y ≤ φ z := hmono hzIcc.1
    have hzx : φ z ≤ φ x := hmono hzIcc.2
    constructor
    · intro hzTop
      exact hxTop (top_le_iff.mp (hzTop ▸ hzx))
    · intro hzBot
      exact hyBot (le_bot_iff.mp (hzBot ▸ hyz))

/-- The finite-valued interval of a monotone profile is convex. -/
lemma helperForTheorem_5_24_4_finiteValueSet_convex
    (φ : ℝ → EReal) (hmono : Monotone φ) :
    Convex ℝ (oneDimensionalPrimitiveFiniteValueSet φ) := by
  intro x hx y hy α β hα hβ hsum
  by_cases hxy : x ≤ y
  · have hmem : α • x + β • y ∈ Set.Icc x y := by
      constructor
      · have hnonneg : 0 ≤ β * (y - x) := by
          exact mul_nonneg hβ (sub_nonneg.mpr hxy)
        have hαeq : α = 1 - β := by
          linarith
        rw [smul_eq_mul, smul_eq_mul]
        calc
          x ≤ x + β * (y - x) := by linarith
          _ = α * x + β * y := by
              rw [hαeq]
              ring
      · have hnonneg : 0 ≤ α * (y - x) := by
          exact mul_nonneg hα (sub_nonneg.mpr hxy)
        have hβeq : β = 1 - α := by
          linarith
        rw [smul_eq_mul, smul_eq_mul]
        calc
          α * x + β * y = y - α * (y - x) := by
              rw [hβeq]
              ring
          _ ≤ y := by linarith
    exact helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
      (by simpa [Set.uIcc_of_le hxy] using hmem)
  · have hyx : y ≤ x := le_of_not_ge hxy
    have hmem : α • x + β • y ∈ Set.Icc y x := by
      constructor
      · have hnonneg : 0 ≤ α * (x - y) := by
          exact mul_nonneg hα (sub_nonneg.mpr hyx)
        have hβeq : β = 1 - α := by
          linarith
        rw [smul_eq_mul, smul_eq_mul]
        calc
          y ≤ y + α * (x - y) := by linarith
          _ = α * x + β * y := by
              rw [hβeq]
              ring
      · have hnonneg : 0 ≤ β * (x - y) := by
          exact mul_nonneg hβ (sub_nonneg.mpr hyx)
        have hαeq : α = 1 - β := by
          linarith
        rw [smul_eq_mul, smul_eq_mul]
        calc
          α * x + β * y = x - β * (x - y) := by
              rw [hαeq]
              ring
          _ ≤ x := by linarith
    exact helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
      (by simpa [Set.uIcc_of_ge hyx] using hmem)

/-- If two endpoints are finite-valued, then every strict intermediate point is finite-valued. -/
lemma helperForTheorem_5_24_4_finite_on_open_interval_of_finite_endpoints
    (φ : ℝ → EReal) (hmono : Monotone φ) {x y : ℝ}
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    ∀ t ∈ Set.uIoo x y, t ∈ oneDimensionalPrimitiveFiniteValueSet φ := by
  intro t ht
  exact helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy
    (Set.uIoo_subset_uIcc_self ht)

/-- On a finite-valued unordered interval, `φ.toReal` is monotone. -/
lemma helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
    (φ : ℝ → EReal) (hmono : Monotone φ) {x y : ℝ}
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hy : y ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    MonotoneOn (fun t : ℝ => (φ t).toReal) (Set.uIcc x y) := by
  intro u hu v hv huv
  have huFinite :
      u ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy hu
  have hvFinite :
      v ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
    helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono hx hy hv
  exact EReal.toReal_le_toReal (hmono huv) huFinite.2 hvFinite.1

/-- If the endpoints are finite-valued, the primitive is the genuine real interval integral. -/
lemma helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a x =
      (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
  have hFiniteOpen :
      ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal) :=
    helperForTheorem_5_24_4_finite_on_open_interval_of_finite_endpoints
      φ hmono ha hx
  have hMonoToReal :
      MonotoneOn (fun t : ℝ => (φ t).toReal) (Set.uIcc a x) :=
    helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hx
  have hInt :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x :=
    hMonoToReal.intervalIntegrable
  dsimp [oneDimensionalIntervalIntegralPrimitiveValue]
  split_ifs with hOpen'
  · rfl
  · exact (hOpen' hFiniteOpen).elim

/-- On any scalar interval whose endpoints are finite for the monotone profile, the interval
integral primitive is continuous. -/
lemma helperForTheorem_5_24_4_primitiveValue_continuousOn_uIcc_of_finite_endpoints
    (φ : ℝ → EReal) (a x : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hx : x ∈ oneDimensionalPrimitiveFiniteValueSet φ) :
    ContinuousOn (oneDimensionalIntervalIntegralPrimitiveValue φ a) (Set.uIcc a x) := by
  have hMonoToReal :
      MonotoneOn (fun t : ℝ => (φ t).toReal) (Set.uIcc a x) :=
    helperForTheorem_5_24_4_toReal_monotoneOn_uIcc_of_finite_endpoints
      φ hmono ha hx
  have hInt :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x :=
    hMonoToReal.intervalIntegrable
  have hContIntReal :
      ContinuousOn (fun z : ℝ => ∫ t in a..z, (φ t).toReal) (Set.uIcc a x) :=
    intervalIntegral.continuousOn_primitive_interval' hInt (by simp)
  have hContInt :
      ContinuousOn (fun z : ℝ => (((∫ t in a..z, (φ t).toReal) : ℝ) : EReal)) (Set.uIcc a x) :=
    continuous_coe_real_ereal.comp_continuousOn hContIntReal
  have hEq :
      Set.EqOn (oneDimensionalIntervalIntegralPrimitiveValue φ a)
        (fun z : ℝ => (((∫ t in a..z, (φ t).toReal) : ℝ) : EReal)) (Set.uIcc a x) := by
    intro z hz
    have hzFinite :
        z ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
      helperForTheorem_5_24_4_finiteValueSet_mem_between φ hmono ha hx hz
    exact helperForTheorem_5_24_4_primitiveValue_eq_integral_of_finite_endpoints
      φ a z hmono ha hzFinite
  exact hContInt.congr hEq

/-- A scalar effective-domain point of the interval-integral primitive automatically carries the
two hidden ingredients in the definition: finiteness of the open interval profile and interval
integrability of `φ.toReal`. -/
lemma helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    (∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal)) ∧
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x := by
  have hxNotTop :
      oneDimensionalIntervalIntegralPrimitiveValue φ a x ≠ (⊤ : EReal) := by
    have hxLtTop :
        oneDimensionalIntervalIntegralPrimitiveValue φ a x < (⊤ : EReal) := by
      simpa [scalarEffectiveDomain, effectiveDomain_eq,
        helperForTheorem_5_24_4_scalarPoint_primitive_eval] using hxDom
    exact (lt_top_iff_ne_top).1 hxLtTop
  by_cases hOpen :
      ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal)
  · by_cases hInt :
        IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x
    · refine ⟨?_, hInt⟩
      intro t ht
      exact hOpen t ht
    · exfalso
      exact hxNotTop (by simp [oneDimensionalIntervalIntegralPrimitiveValue, hOpen, hInt])
  · exfalso
    exact hxNotTop (by simp [oneDimensionalIntervalIntegralPrimitiveValue, hOpen])

/-- On any scalar effective-domain point, the interval-integral primitive is exactly the real
interval integral encoded into `EReal`. -/
lemma helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
    (φ : ℝ → EReal) (a x : ℝ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a x =
      (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨hOpen, hInt⟩
  dsimp [oneDimensionalIntervalIntegralPrimitiveValue]
  by_cases hOpen' :
      ∀ t ∈ Set.uIoo a x, φ t ≠ (⊤ : EReal) ∧ φ t ≠ (⊥ : EReal)
  · by_cases hInt' :
        IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume a x
    · rw [if_pos hOpen', if_pos hInt']
    · exact (hInt' hInt).elim
  · exact (hOpen' hOpen).elim

/-- Any strict point between two scalar effective-domain points of the primitive carries a finite
profile value. This is the interval `J` from the proof of Theorem 5.24.4. -/
lemma helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
    (φ : ℝ → EReal) (a x y t : ℝ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (ht : t ∈ Set.uIoo x y) :
    t ∈ oneDimensionalPrimitiveFiniteValueSet φ := by
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨hOpenX, _⟩
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a y hyDom with
    ⟨hOpenY, _⟩
  by_cases hxy : x ≤ y
  · have htIoo : t ∈ Set.Ioo x y := by
      simpa [Set.uIoo_of_le hxy] using ht
    by_cases hta : t < a
    · have hmem : t ∈ Set.uIoo a x := by
        have hxa : x < a := lt_trans htIoo.1 hta
        simpa [Set.uIoo_of_ge hxa.le] using (show t ∈ Set.Ioo x a from ⟨htIoo.1, hta⟩)
      exact hOpenX t hmem
    · by_cases hat : a < t
      · have hmem : t ∈ Set.uIoo a y := by
          have hay : a < y := lt_trans hat htIoo.2
          simpa [Set.uIoo_of_le hay.le] using (show t ∈ Set.Ioo a y from ⟨hat, htIoo.2⟩)
        exact hOpenY t hmem
      · have htaEq : t = a := le_antisymm (le_of_not_gt hat) (le_of_not_gt hta)
        simpa [htaEq] using ha
  · have hyx : y ≤ x := le_of_not_ge hxy
    have htIoo : t ∈ Set.Ioo y x := by
      simpa [Set.uIoo_of_ge hyx] using ht
    by_cases hta : t < a
    · have hmem : t ∈ Set.uIoo a y := by
        have hya : y < a := lt_trans htIoo.1 hta
        simpa [Set.uIoo_of_ge hya.le] using (show t ∈ Set.Ioo y a from ⟨htIoo.1, hta⟩)
      exact hOpenY t hmem
    · by_cases hat : a < t
      · have hmem : t ∈ Set.uIoo a x := by
          have hax : a < x := lt_trans hat htIoo.2
          simpa [Set.uIoo_of_le hax.le] using (show t ∈ Set.Ioo a x from ⟨hat, htIoo.2⟩)
        exact hOpenX t hmem
      · have htaEq : t = a := le_antisymm (le_of_not_gt hat) (le_of_not_gt hta)
        simpa [htaEq] using ha

/-- Two scalar effective-domain points of the primitive bound an interval on which `φ.toReal` is
interval-integrable. -/
lemma helperForTheorem_5_24_4_intervalIntegrable_toReal_of_domain_points
    (φ : ℝ → EReal) (a x y : ℝ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x y := by
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨_, hIntX⟩
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a y hyDom with
    ⟨_, hIntY⟩
  exact hIntX.symm.trans hIntY

/-- Between two scalar effective-domain points, the primitive increment is exactly the interval
integral of `φ.toReal`, even if one of the endpoints lies on the boundary of the finite interval
`J`. -/
lemma helperForTheorem_5_24_4_primitiveValue_sub_eq_integral_of_domain_points
    (φ : ℝ → EReal) (a x y : ℝ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a)) :
    oneDimensionalIntervalIntegralPrimitiveValue φ a y -
      oneDimensionalIntervalIntegralPrimitiveValue φ a x =
        (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := by
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a x hxDom with
    ⟨_, hIntX⟩
  rcases
      helperForTheorem_5_24_4_openFinite_and_intervalIntegrable_of_mem_scalarEffectiveDomain
        φ a y hyDom with
    ⟨_, hIntY⟩
  have hSub :
      (((∫ t in a..y, (φ t).toReal : ℝ) : ℝ) : EReal) -
          (((∫ t in a..x, (φ t).toReal : ℝ) : ℝ) : EReal) =
        (((((∫ t in a..y, (φ t).toReal : ℝ) : ℝ) -
            ∫ t in a..x, (φ t).toReal : ℝ) : ℝ) : EReal) := by
    simp [EReal.coe_sub]
  calc
    oneDimensionalIntervalIntegralPrimitiveValue φ a y -
        oneDimensionalIntervalIntegralPrimitiveValue φ a x
      = (((∫ t in a..y, (φ t).toReal) : ℝ) : EReal) -
          (((∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := by
          rw [helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
                φ a y hyDom,
              helperForTheorem_5_24_4_primitiveValue_eq_integral_of_mem_scalarEffectiveDomain
                φ a x hxDom]
    _ = (((((∫ t in a..y, (φ t).toReal) : ℝ) -
            ∫ t in a..x, (φ t).toReal) : ℝ) : EReal) := hSub
    _ = (((∫ t in x..y, (φ t).toReal) : ℝ) : EReal) := by
      exact congrArg (fun r : ℝ => (r : EReal))
        (intervalIntegral.integral_interval_sub_left hIntY hIntX)

/-- On a domain segment `(x, z)` whose interior points are finite and whose right endpoint carries
a finite profile value, the interval integral is bounded above by the right endpoint profile. -/
lemma helperForTheorem_5_24_4_integral_le_profile_mul_sub_of_domain_lt
    (φ : ℝ → EReal) (a x z : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxDom : x ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hzDom : z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hzFinite : z ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hxz : x < z) :
    (((∫ t in x..z, (φ t).toReal) : ℝ) : EReal) ≤
      ((((z - x) * (φ z).toReal : ℝ) : EReal)) := by
  have hIntxz :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume x z :=
    helperForTheorem_5_24_4_intervalIntegrable_toReal_of_domain_points φ a x z hxDom hzDom
  have hLeReal :
      (∫ t in x..z, (φ t).toReal) ≤ (z - x) * (φ z).toReal := by
    have hLe :
        (∫ t in x..z, (φ t).toReal) ≤ ∫ t in x..z, (φ z).toReal := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (μ := MeasureTheory.volume) (a := x) (b := z)
        (f := fun t : ℝ => (φ t).toReal) (g := fun _ : ℝ => (φ z).toReal)
        (le_of_lt hxz) hIntxz ?_ ?_
      · simp
      · intro t ht
        have htFinite :
            t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
          helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
            φ a x z t ha hxDom hzDom (by simpa [Set.uIoo_of_lt hxz] using ht)
        exact EReal.toReal_le_toReal (hmono (le_of_lt ht.2)) htFinite.2 hzFinite.1
    calc
      (∫ t in x..z, (φ t).toReal) ≤ ∫ t in x..z, (φ z).toReal := hLe
      _ = (z - x) * (φ z).toReal := by
        norm_num [intervalIntegral.integral_const, hxz.le, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  exact_mod_cast hLeReal

/-- On a domain segment `(z, y)` whose interior points are finite and whose left endpoint carries
a finite profile value, the interval integral dominates the left endpoint profile. -/
lemma helperForTheorem_5_24_4_profile_mul_sub_le_integral_of_domain_lt
    (φ : ℝ → EReal) (a z y : ℝ) (hmono : Monotone φ)
    (ha : a ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hzDom : z ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hyDom : y ∈ scalarEffectiveDomain (oneDimensionalIntervalIntegralPrimitive φ a))
    (hzFinite : z ∈ oneDimensionalPrimitiveFiniteValueSet φ)
    (hzy : z < y) :
    ((((y - z) * (φ z).toReal : ℝ) : EReal)) ≤
      (((∫ t in z..y, (φ t).toReal) : ℝ) : EReal) := by
  have hIntzy :
      IntervalIntegrable (fun t : ℝ => (φ t).toReal) MeasureTheory.volume z y :=
    helperForTheorem_5_24_4_intervalIntegrable_toReal_of_domain_points φ a z y hzDom hyDom
  have hLeReal :
      (y - z) * (φ z).toReal ≤ (∫ t in z..y, (φ t).toReal) := by
    have hLe :
        (∫ t in z..y, (φ z).toReal) ≤ ∫ t in z..y, (φ t).toReal := by
      refine intervalIntegral.integral_mono_on_of_le_Ioo
        (μ := MeasureTheory.volume) (a := z) (b := y)
        (f := fun _ : ℝ => (φ z).toReal) (g := fun t : ℝ => (φ t).toReal)
        (le_of_lt hzy) ?_ hIntzy ?_
      · simp
      · intro t ht
        have htFinite :
            t ∈ oneDimensionalPrimitiveFiniteValueSet φ :=
          helperForTheorem_5_24_4_finite_profile_on_open_interval_of_domain_points
            φ a z y t ha hzDom hyDom (by simpa [Set.uIoo_of_lt hzy] using ht)
        exact EReal.toReal_le_toReal (hmono (le_of_lt ht.1)) hzFinite.2 htFinite.1
    calc
      (y - z) * (φ z).toReal = ∫ t in z..y, (φ z).toReal := by
        norm_num [intervalIntegral.integral_const, hzy.le, sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
      _ ≤ (∫ t in z..y, (φ t).toReal) := hLe
  exact_mod_cast hLeReal

end Section24
end Chap05
