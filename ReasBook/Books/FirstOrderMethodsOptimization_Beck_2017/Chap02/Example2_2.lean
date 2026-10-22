/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/-- The extended-real-valued example that equals `1 / x` on the positive ray and `∞` elsewhere. -/
def positive_reciprocal_barrier : ℝ → EReal :=
  fun x ↦ if 0 < x then ((1 / x : ℝ) : EReal) else ⊤

-- Proof sketch: this is the defining equation of `positive_reciprocal_barrier`.
/-- Evaluating `positive_reciprocal_barrier` at `x` gives the textbook piecewise formula. -/
@[simp] theorem positive_reciprocal_barrier_apply (x : ℝ) :
    positive_reciprocal_barrier x = if 0 < x then ((1 / x : ℝ) : EReal) else ⊤ :=
  rfl

-- Proof sketch: simplify the defining `if` on the branch `0 < x`.
/-- On the positive ray, `positive_reciprocal_barrier` agrees with the finite branch `1 / x`. -/
theorem positive_reciprocal_barrier_of_pos {x : ℝ} (hx : 0 < x) :
    positive_reciprocal_barrier x = ((1 / x : ℝ) : EReal) := by
  simp [positive_reciprocal_barrier, hx]

-- Proof sketch: simplify the defining `if` on the complementary branch `x ≤ 0`.
/-- Outside the positive ray, `positive_reciprocal_barrier` takes the value `∞`. -/
theorem positive_reciprocal_barrier_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    positive_reciprocal_barrier x = ⊤ := by
  simp [positive_reciprocal_barrier, hx]

-- Proof sketch: unfold `positive_reciprocal_barrier`; for `x > 0` the value is the finite real
-- `1 / x`, while for `x ≤ 0` the value is `⊤`, so the finite-value locus is exactly `Set.Ioi 0`.
/-- The finite-value domain of `positive_reciprocal_barrier` is exactly the open ray `(0, ∞)`. -/
theorem positive_reciprocal_barrier_effective_domain_eq :
    effective_domain positive_reciprocal_barrier = Set.Ioi (0 : ℝ) := by
  -- Normalize the effective domain by splitting on the defining branch condition `0 < x`.
  ext x
  by_cases hx : 0 < x <;> simp [effective_domain, positive_reciprocal_barrier, hx]

/-- A real number lies in the effective domain of `positive_reciprocal_barrier` exactly when it is
positive. -/
@[simp] theorem mem_effective_domain_positive_reciprocal_barrier (x : ℝ) :
    x ∈ effective_domain positive_reciprocal_barrier ↔ 0 < x := by
  rw [positive_reciprocal_barrier_effective_domain_eq]
  rfl

-- Proof sketch: rewrite the effective domain using
-- `positive_reciprocal_barrier_effective_domain_eq`, then use that `Set.Ioi (0 : ℝ)` is open and
-- not closed in `ℝ`.
/-- The effective domain of `positive_reciprocal_barrier` is not closed. -/
theorem positive_reciprocal_barrier_effective_domain_not_closed :
    ¬ IsClosed (effective_domain positive_reciprocal_barrier) := by
  -- Rewrite to the open ray and use that its closure contains `0`.
  rw [positive_reciprocal_barrier_effective_domain_eq]
  intro hClosed
  have hmem : (0 : ℝ) ∈ Set.Ioi (0 : ℝ) := by
    rw [← hClosed.closure_eq, closure_Ioi]
    simp
  exact (lt_irrefl (0 : ℝ)) hmem

-- Proof sketch: split on the sign of `p.1`. For `p.1 ≤ 0`, the left side is impossible because
-- `positive_reciprocal_barrier p.1 = ⊤` cannot be bounded above by a real number. For `p.1 > 0`,
-- simplify the inequality `1 / p.1 ≤ p.2` by multiplying through by the positive factor `p.1`.
/-- The source-facing real epigraph of `positive_reciprocal_barrier` is the set
`{(x, y) | 0 < x ∧ 1 ≤ x * y}`. -/
theorem positive_reciprocal_barrier_real_epigraph_eq :
    realEpigraph positive_reciprocal_barrier =
      {p : ℝ × ℝ | 0 < p.1 ∧ (1 : ℝ) ≤ p.1 * p.2} := by
  ext p
  by_cases hx : 0 < p.1
  · -- On the positive branch, convert the `EReal` inequality back to a real inequality.
    constructor
    · intro hp
      have hp' : ((1 / p.1 : ℝ) : EReal) ≤ (p.2 : EReal) := by
        simpa [realEpigraph, positive_reciprocal_barrier, hx] using hp
      refine ⟨hx, ?_⟩
      have hp'' : (1 / p.1 : ℝ) ≤ p.2 := EReal.coe_le_coe_iff.mp hp'
      have : (1 : ℝ) ≤ p.2 * p.1 := (div_le_iff₀ hx).mp hp''
      simpa [mul_comm] using this
    · rintro ⟨_, hp⟩
      have hp' : (1 : ℝ) ≤ p.2 * p.1 := by
        simpa [mul_comm] using hp
      have hp'' : (1 / p.1 : ℝ) ≤ p.2 := (div_le_iff₀ hx).mpr hp'
      have hcoe : ((1 / p.1 : ℝ) : EReal) ≤ (p.2 : EReal) := EReal.coe_le_coe_iff.mpr hp''
      simpa [realEpigraph, positive_reciprocal_barrier, hx] using hcoe
  · -- On the nonpositive branch, the barrier value is `⊤`, so no real point lies above it.
    simp [realEpigraph, positive_reciprocal_barrier, hx]

/-- A point `(x, y)` lies in the real epigraph of `positive_reciprocal_barrier` exactly when
`x > 0` and `1 ≤ x * y`. -/
@[simp] theorem mem_realEpigraph_positive_reciprocal_barrier_iff (x y : ℝ) :
    (x, y) ∈ realEpigraph positive_reciprocal_barrier ↔ 0 < x ∧ (1 : ℝ) ≤ x * y := by
  rw [positive_reciprocal_barrier_real_epigraph_eq]
  rfl

-- Proof sketch: prove closedness for the canonical owner `realEpigraph positive_reciprocal_barrier`
-- either directly from `positive_reciprocal_barrier_real_epigraph_eq` and continuity of
-- multiplication, or via `lowerSemicontinuous_iff_isClosed_real_epigraph`.
/-- Example2.2: the real epigraph of the positive reciprocal barrier is closed, even though its
effective domain is the open ray `(0, ∞)`. -/
theorem positive_reciprocal_barrier_real_epigraph_is_closed :
    IsClosed (realEpigraph positive_reciprocal_barrier) := by
  -- First rewrite the epigraph to its geometric description from the source text.
  rw [positive_reciprocal_barrier_real_epigraph_eq]
  have hrewrite :
      {p : ℝ × ℝ | 0 < p.1 ∧ (1 : ℝ) ≤ p.1 * p.2} =
        {p : ℝ × ℝ | (0 : ℝ) ≤ p.1 ∧ (1 : ℝ) ≤ p.1 * p.2} := by
    ext p
    constructor
    · intro hp
      exact ⟨le_of_lt hp.1, hp.2⟩
    · intro hp
      change (0 : ℝ) ≤ p.1 ∧ (1 : ℝ) ≤ p.1 * p.2 at hp
      have hne : (0 : ℝ) ≠ p.1 := by
        intro hzero
        rw [← hzero] at hp
        norm_num at hp
      exact ⟨lt_of_le_of_ne hp.1 hne, hp.2⟩
  rw [hrewrite]
  -- The normalized set is an intersection of two closed half-space conditions.
  have hnonneg : IsClosed {p : ℝ × ℝ | (0 : ℝ) ≤ p.1} :=
    isClosed_le continuous_const continuous_fst
  have hmul : IsClosed {p : ℝ × ℝ | (1 : ℝ) ≤ p.1 * p.2} :=
    isClosed_le continuous_const (continuous_fst.mul continuous_snd)
  have hinter :
      IsClosed
        ({p : ℝ × ℝ | (0 : ℝ) ≤ p.1} ∩ {p : ℝ × ℝ | (1 : ℝ) ≤ p.1 * p.2}) :=
    hnonneg.inter hmul
  simpa [Set.setOf_and] using hinter

-- Proof sketch: use the canonical equivalence between lower semicontinuity and closedness of the
-- epigraph in `ℝ × EReal`, or add the `⊤`-slice to the real epigraph and check that this enlarged
-- set is closed.
/-- The extended-real epigraph of `positive_reciprocal_barrier` is closed. -/
theorem positive_reciprocal_barrier_epigraph_is_closed :
    IsClosed {p : ℝ × EReal | positive_reciprocal_barrier p.1 ≤ p.2} := by
  -- Transport the real-epigraph result through the lower-semicontinuity equivalence.
  have h_lsc : LowerSemicontinuous positive_reciprocal_barrier := by
    rw [lowerSemicontinuous_iff_isClosed_real_epigraph]
    exact positive_reciprocal_barrier_real_epigraph_is_closed
  exact h_lsc.isClosed_epigraph

-- Proof sketch: apply `lowerSemicontinuous_iff_isClosed_epigraph` to
-- `positive_reciprocal_barrier_epigraph_is_closed`.
/-- The positive reciprocal barrier is lower semicontinuous, anticipating the later equivalence
between lower semicontinuity and closedness. -/
theorem positive_reciprocal_barrier_lowerSemicontinuous :
    LowerSemicontinuous positive_reciprocal_barrier := by
  -- Reuse the closed real epigraph characterization already established above.
  rw [lowerSemicontinuous_iff_isClosed_real_epigraph]
  exact positive_reciprocal_barrier_real_epigraph_is_closed

end
