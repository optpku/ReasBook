/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import Mathlib.Data.Nat.Lattice

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

/- Definition 5.2.10 lies in the Chapter 5 strongly-convex multistage-acceleration threshold
domain.

Sampled owner-style declarations before refining:
* `IsLeast` in mathlib `Order.Bounds.Defs`, the canonical least-element owner;
* `Nat.sInf_mem` and `Nat.sInf_le` in `Mathlib/Data/Nat/Lattice`, the canonical `ℕ` API for a
  least element of a nonempty set;
* `GeneralIterativeScheme.IsAnalyticalComplexity` in `Chap01/Definition_1_2_11`, the chapter's
  earlier source-facing use of `IsLeast` for a first admissible natural index.

Source/core/bridge triage:
* source-facing: the admissible half-gap index set and the textbook threshold index `k_p`;
* core/canonical: `IsLeast` for the least admissible natural number;
* bridge/view: the explicit membership formula for the admissible set.

Primitive data:
* the admissible-index set cut out by the source inequality.

Derived API:
* the least admissible index `stronglyConvexHalfGapIndex`;
* its canonical least-element certificate;
* the positivity consequence `1 ≤ stronglyConvexHalfGapIndex ...` under nonemptiness.

This refinement keeps the source-facing `k_p` object while deleting the local duplicate wheel API
for least elements in favor of the canonical `IsLeast` owner theorem. -/

/-- The set of positive iteration counts `k ≥ 1` for which the strong-convexity global-rate bound
`2^(5/2) * c * M_f * (f(x₀) - f*)^(3/2) / k^p` is already at most half of the initial
suboptimality `f(x₀) - f*`. -/
def stronglyConvexHalfGapAdmissibleIndices
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) : Set ℕ :=
  {k | 1 ≤ k ∧
    (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
        Real.rpow (k : ℝ) p ≤
      initialGap / 2}

-- Proof sketch: unfold `stronglyConvexHalfGapAdmissibleIndices`; membership is exactly the
-- displayed inequality from the definition.
/-- Membership in `stronglyConvexHalfGapAdmissibleIndices c M_f p Δ₀` is equivalent to saying
that `k` is positive and satisfies the displayed half-gap inequality. -/
@[simp] theorem mem_stronglyConvexHalfGapAdmissibleIndices_iff
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) (k : ℕ) :
    k ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap ↔
      1 ≤ k ∧
        (Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)) /
            Real.rpow (k : ℝ) p ≤
          initialGap / 2 :=
  Iff.rfl

-- Proof sketch: if `initialGap > 0` and `p > 0`, then `k ↦ k^p` tends to `+∞`, so the displayed
-- inequality eventually holds; the positivity side condition is handled by choosing `k ≥ 1`.
/-- Definition 5.2.10: for a positive initial gap and exponent `p > 0`, the half-gap admissible
index set is nonempty. This is the canonical existence API used to discharge the auxiliary witness
behind the source threshold index `k_p`. -/
theorem stronglyConvexHalfGapAdmissibleIndices_nonempty
    {c p initialGap : ℝ} {Mf : NNReal} (hp : 0 < p) (hgap : 0 < initialGap) :
    (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty := by
  -- Freeze the numerator of the displayed rate bound so the proof splits on its sign only once.
  let A :=
    Real.rpow (2 : ℝ) (5 / 2 : ℝ) * c * (Mf : ℝ) * Real.rpow initialGap (3 / 2 : ℝ)
  have hhalf : 0 < initialGap / 2 := by
    linarith
  by_cases hA : A ≤ 0
  · -- If the numerator is nonpositive, the first positive index `k = 1` is already admissible.
    refine ⟨1, ?_⟩
    rw [mem_stronglyConvexHalfGapAdmissibleIndices_iff]
    constructor
    · norm_num
    · have hden : 0 < Real.rpow (1 : ℝ) p := by
        exact Real.rpow_pos_of_pos (by norm_num) p
      have hfrac : A / Real.rpow (1 : ℝ) p ≤ 0 := by
        exact div_nonpos_of_nonpos_of_nonneg hA hden.le
      have htarget : A / Real.rpow (1 : ℝ) p ≤ initialGap / 2 := by
        exact le_trans hfrac hhalf.le
      simpa [A] using htarget
  · -- Otherwise `k ↦ k^p` tends to `+∞`, so some positive denominator dominates the threshold.
    have ht :
        Filter.Tendsto (fun k : ℕ ↦ Real.rpow (k : ℝ) p) Filter.atTop Filter.atTop := by
      simpa using (tendsto_rpow_atTop hp).comp tendsto_natCast_atTop_atTop
    obtain ⟨N, hN⟩ := Filter.tendsto_atTop_atTop.mp ht (A / (initialGap / 2))
    refine ⟨N + 1, ?_⟩
    rw [mem_stronglyConvexHalfGapAdmissibleIndices_iff]
    constructor
    · exact Nat.succ_le_succ (Nat.zero_le N)
    · have hkden : 0 < Real.rpow ((N + 1 : ℕ) : ℝ) p := by
        have hkpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by
          positivity
        exact Real.rpow_pos_of_pos hkpos p
      have hbound : A / (initialGap / 2) ≤ Real.rpow ((N + 1 : ℕ) : ℝ) p := by
        exact hN (N + 1) (Nat.le_succ N)
      have hmul' : A ≤ Real.rpow ((N + 1 : ℕ) : ℝ) p * (initialGap / 2) := by
        exact (div_le_iff₀ hhalf).1 hbound
      have hmul : A ≤ (initialGap / 2) * Real.rpow ((N + 1 : ℕ) : ℝ) p := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmul'
      have htarget : A / Real.rpow ((N + 1 : ℕ) : ℝ) p ≤ initialGap / 2 := by
        exact (div_le_iff₀ hkden).2 hmul
      simpa [A] using htarget

/-- The threshold index from Definition 5.2.10: when the positive admissible-index set is
nonempty, `stronglyConvexHalfGapIndex c M_f p (f(x₀) - f*)` is the first positive integer
`k_p ≥ 1` for which the global-rate bound
`2^(5/2) * c * M_f * (f(x₀) - f*)^(3/2) / k^p ≤ (f(x₀) - f*) / 2` holds. -/
def stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) : ℕ :=
  sInf (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap)

/- Source-facing Lean notation for the textbook threshold index `k_p`. -/
scoped[StronglyConvexHalfGapIndex] notation:max
  "k[" c ", " Mf "; " p "](" initialGap ")" =>
    stronglyConvexHalfGapIndex c Mf p initialGap

open scoped StronglyConvexHalfGapIndex

-- Proof sketch: unfold `stronglyConvexHalfGapIndex` and apply `Nat.sInf_mem` to the admissible
-- index set.
/-- If the positive admissible-index set is nonempty, then the textbook threshold index
`k[c, M_f; p](Δ₀)` is its least element. -/
theorem isLeast_stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ)
    (hnonempty : (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty) :
    IsLeast
      (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap)
      (k[c, Mf; p](initialGap)) := by
  refine ⟨Nat.sInf_mem hnonempty, fun k hk ↦ Nat.sInf_le hk⟩

-- Proof sketch: extract the positivity clause from the least-element certificate
-- `isLeast_stronglyConvexHalfGapIndex`.
/-- If the positive admissible-index set is nonempty, then the textbook threshold index
`k[c, M_f; p](Δ₀)` is itself positive. -/
theorem one_le_stronglyConvexHalfGapIndex
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ)
    (hnonempty : (stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap).Nonempty) :
    1 ≤ k[c, Mf; p](initialGap) := by
  exact (isLeast_stronglyConvexHalfGapIndex c Mf p initialGap hnonempty).1.1

-- Proof sketch: any admissible positive index belongs to the defining set, so the least
-- admissible index `k_p` is bounded above by it.
/-- Any admissible positive index bounds the textbook threshold index
`k[c, M_f; p](Δ₀)` from above. This is the canonical source-facing consequence of the least-index
owner API. -/
theorem stronglyConvexHalfGapIndex_le_of_mem
    (c : ℝ) (Mf : NNReal) (p initialGap : ℝ) {k : ℕ}
    (hk : k ∈ stronglyConvexHalfGapAdmissibleIndices c Mf p initialGap) :
    k[c, Mf; p](initialGap) ≤ k := by
  exact (isLeast_stronglyConvexHalfGapIndex c Mf p initialGap ⟨k, hk⟩).2 hk
