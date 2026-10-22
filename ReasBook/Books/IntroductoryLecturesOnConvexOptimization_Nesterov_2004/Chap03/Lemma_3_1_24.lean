/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_23

-- Declarations for this item will be appended below by the statement pipeline.

open Filter

universe u v

section

variable {E : Type u} {U : Type v}

/- Lemma 3.1.24 lies in the chapter's primal-dual gap domain.

Primary domain:
- stagewise primal-dual gap bounds from certificate maxima and weak duality

Sampled owner-style declarations:
- `primal_dual_decomposition_mem_Icc_of_gap_le` in `Chap03/Lemma_3_1_23`, the generic
  interval owner for one primal-dual gap value;
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_max` in
  `Chap03/Lemma_3_24`, the neighboring source-facing max-attainment specialization of that
  interval owner;
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_sSup` in
  `Chap03/Lemma_3_24`, the corresponding canonical `sSup` companion theorem;
- `IsGreatest.csSup_eq` in mathlib, the canonical bridge from an explicit maximum-attainment
  statement to the corresponding supremum equality.

Best owner abstraction:
- source-facing: the stagewise primal-dual interval bound under an attained certificate maximum
  `δMax N`;
- core/canonical: `primal_dual_decomposition_mem_Icc_of_gap_le`;
- bridge/view: the canonical `sSup (δ N '' P)` reformulations obtained from `(hδMax N).csSup_eq`.

Primitive data:
- the certificate family `δ`
- the set `P`
- the scalar sequences `hatf`, `uHat`, `r`
- the comparison values `fStar`, `φStar`
- the source-facing maximum values `δMax`

Derived API:
- the local primal comparison `fStar ≤ hatf N`
- the stagewise dual comparison `φ (uHat N) ≤ φStar`
- weak duality `φStar ≤ fStar`
- the canonical supremum view `sSup (δ N '' P)` of the attained maxima

Source/core/bridge triage:
- source-facing: the textbook stagewise estimate and its convergence consequence expressed through
  an attained maximum `δMax N`;
- core/canonical: `primal_dual_decomposition_mem_Icc_of_gap_le`
- bridge/view: the companion `sSup` interval and convergence reformulations

The interval/decomposition owner already lives in `Lemma_3_1_23`, so this file keeps the
attained-maximum statement primary and retains the `sSup` formulations only as companion
canonical views. -/

section

variable {P : Set E}
variable (δ : ℕ → E → ℝ) (hatf : ℕ → ℝ) (φ : U → ℝ) (uHat : ℕ → U)
variable (fStar φStar : ℝ) (r : ℕ → ℝ)
variable
    (h_primal_lower : ∀ N, fStar ≤ hatf N)
    (h_dual_upper_uHat : ∀ N, φ (uHat N) ≤ φStar)
    (h_weak_duality : φStar ≤ fStar)

include h_primal_lower h_dual_upper_uHat h_weak_duality

local notation "gap" =>
  fun N ↦ hatf N - φ (uHat N)

local notation "decomposition" =>
  fun N ↦ (hatf N - fStar) + (φStar - φ (uHat N))

/-- Helper for Lemma 3.1.24: the canonical `sSup` bounds imply both the interval control for the
stagewise decomposition and the stagewise `r_N` bound on the primal-dual gap. -/
-- Proof sketch: combine the two `sSup` inequalities into `gap N ≤ r N`, then invoke the generic
-- owner theorem from Lemma 3.1.23 for the fixed stage `N`.
private theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  simpa using
    (primal_dual_decomposition_mem_Icc_of_gap_le
      (h_primal_lower N)
      (h_dual_upper_uHat N)
      h_weak_duality
      (le_trans (h_gap_le_sSup_delta N) (h_sSup_delta_le N)))

/-- Lemma 3.1.24: if the stagewise gap is bounded by an attained certificate maximum `δMax N`,
and these maxima satisfy `δMax N ≤ r_N`, then for every stage `N` the decomposition
`(\hat f_N - f^*) + (\phi^* - φ(\hat u_N))` lies in the interval
`[0, \hat f_N - φ(\hat u_N)]` and the gap itself is bounded by `r_N`. -/
-- Proof sketch: rewrite the attained maxima as the canonical suprema `sSup (δ N '' P)` via
-- `(hδMax N).csSup_eq`, then apply the generic interval owner
-- `primal_dual_decomposition_mem_Icc_of_gap_le` at each single stage `N`.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_max_delta
    (δMax : ℕ → ℝ)
    (hδMax : ∀ N, IsGreatest (δ N '' P) (δMax N))
    (h_gap_le_δMax : ∀ N, hatf N - φ (uHat N) ≤ δMax N)
    (h_δMax_le : ∀ N, δMax N ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  have h_gap_le_sSup_delta : ∀ n, hatf n - φ (uHat n) ≤ sSup (δ n '' P) := by
    intro n
    simpa [(hδMax n).csSup_eq] using h_gap_le_δMax n
  have h_sSup_delta_le : ∀ n, sSup (δ n '' P) ≤ r n := by
    intro n
    simpa [(hδMax n).csSup_eq] using h_δMax_le n
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N)

/-- Companion canonical `sSup` reformulation of Lemma 3.1.24. -/
-- Proof sketch: combine the stagewise supremum control with the supremum upper bound to get
-- `gap N ≤ r N`, then apply the owner theorem `primal_dual_decomposition_mem_Icc_of_gap_le`
-- at each single stage `N`.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (N : ℕ) :
    decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta_aux
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N)

/-- Companion canonical `sSup` convergence reformulation of Lemma 3.1.24. -/
-- Proof sketch: apply
-- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta` to get
-- `0 ≤ hatf N - φ(\hat u_N) ≤ r_N` for every `N`, then use `squeeze_zero`.
theorem primal_dual_gap_tendsto_zero_of_gap_le_sSup_delta
    (h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P))
    (h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N)
    (hr_tendsto : Tendsto r atTop (nhds 0)) :
    Tendsto gap atTop (nhds 0) := by
  have h_step (N : ℕ) :
      decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N :=
    primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le N
  have h_gap_nonneg : ∀ N, 0 ≤ gap N := by
    intro N
    have h_mem := Set.mem_Icc.mp (h_step N).1
    exact le_trans h_mem.1 h_mem.2
  have h_gap_le_r : ∀ N, gap N ≤ r N := by
    intro N
    exact (h_step N).2
  refine squeeze_zero ?_ ?_ hr_tendsto
  · exact h_gap_nonneg
  · exact h_gap_le_r

/-- If the stagewise gap in Lemma 3.1.24 is controlled by attained certificate maxima `δMax N`
bounded by a sequence `r_N` converging to `0`, then the primal-dual gap itself converges to `0`. -/
-- Proof sketch: rewrite the attained maxima as the canonical suprema `sSup (δ N '' P)` via
-- `(hδMax N).csSup_eq`, then apply the companion `sSup` convergence theorem.
theorem primal_dual_gap_tendsto_zero_of_gap_le_max_delta
    (δMax : ℕ → ℝ)
    (hδMax : ∀ N, IsGreatest (δ N '' P) (δMax N))
    (h_gap_le_δMax : ∀ N, hatf N - φ (uHat N) ≤ δMax N)
    (h_δMax_le : ∀ N, δMax N ≤ r N)
    (hr_tendsto : Tendsto r atTop (nhds 0)) :
    Tendsto gap atTop (nhds 0) := by
  have h_gap_le_sSup_delta : ∀ N, hatf N - φ (uHat N) ≤ sSup (δ N '' P) := by
    intro N
    simpa [(hδMax N).csSup_eq] using h_gap_le_δMax N
  have h_sSup_delta_le : ∀ N, sSup (δ N '' P) ≤ r N := by
    intro N
    simpa [(hδMax N).csSup_eq] using h_δMax_le N
  simpa using
    primal_dual_gap_tendsto_zero_of_gap_le_sSup_delta
      δ hatf φ uHat fStar φStar r h_primal_lower h_dual_upper_uHat h_weak_duality
      h_gap_le_sSup_delta h_sSup_delta_le hr_tendsto

end

end
