/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap03.Lemma_3_1_24

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped BigOperators
open Filter

universe u v

/- Lemma 3.24 lies in the chapter's weighted primal-dual gap / lower-value domain.

Sampled owner-style declarations:
- mathlib `sInf`, the canonical owner for the lower-value slice `u ↦ inf_{x ∈ P} ψ(x, u)`;
- mathlib `dotProduct`, recalled in `Chap03/Definition_3_32`, the scalar owner for
  `∑ k, α k * (...)`;
- mathlib `Finset.centerMass`, the owner behind the weighted dual average;
- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta` in
  `Chap03/Lemma_3_1_24`, the chapter owner turning a raw gap bound into the source interval chain.

Best owner abstraction:
- source-facing: the certificate-controlled weighted gap
  `\hat f_N - inf_{x ∈ P} ψ(x, \hat u_N)`;
- core/canonical: `sInf`, `dotProduct`, and `Finset.centerMass`;
- bridge/view: the certificate image `δ_N '' P` and its attained-maximum specialization.

Primitive data:
- the feasible set `P`;
- the weights `α`, sampled primal points `y`, sampled dual points `u`, kernel `ψ`, and
  certificate field `g`.

Derived API:
- the weighted finite sum `dotProduct α (fun k ↦ ψ (y k) (u k))`;
- the weighted dual average `(Finset.univ).centerMass α u`;
- the canonical lower value
  `sInf ((fun x ↦ ψ x ((Finset.univ).centerMass α u)) '' P)`;
- the gap certificate `gapFunctionCertificate y α g`.

Source/core/bridge triage:
- source-facing: the weighted primal-dual gap and the source interval decomposition from Lemma 3.24;
- core/canonical: the lower-value slice expressed directly through `sInf`;
- bridge/view: the `sSup` / `IsGreatest` certificate bounds controlling that gap.

The previous version made an attained-minimum bridge `φ` the public core statement. This file now
keeps the canonical lower value itself on the theorem surface and treats attainment data only as a
possible bridge behind the scenes. The weighted gap itself is kept only as local notation built
from `hatf`, `uHat`, and `lowerValue`, not as a separate public owner. The remaining hypotheses are
localized to the averaged slices `uHat N` actually used by the gap, instead of imposing a stronger
global attainment package.
-/

section GapFunctionCertificate

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The gap-function certificate `δ_N(x) = ∑_{k=0}^N α_k ⟪g(y_k), y_k - x⟫`. -/
def gapFunctionCertificate {N : ℕ} (y : Fin (N + 1) → V) (α : Fin (N + 1) → ℝ)
    (g : V → V) : V → ℝ :=
  fun x ↦ dotProduct α (fun k ↦ inner ℝ (g (y k)) (y k - x))

/-- Evaluating `gapFunctionCertificate` at `x` gives the defining finite sum
`∑_{k=0}^N α_k ⟪g(y_k), y_k - x⟫`. -/
-- Proof sketch: unfold `gapFunctionCertificate` and `dotProduct`.
theorem gapFunctionCertificate_apply {N : ℕ} (y : Fin (N + 1) → V)
    (α : Fin (N + 1) → ℝ) (g : V → V) (x : V) :
    gapFunctionCertificate y α g x =
      ∑ k, α k * inner ℝ (g (y k)) (y k - x) := by
  simp [gapFunctionCertificate, dotProduct]

end GapFunctionCertificate

section GapFunctionCertificateBound

variable {E : Type u} {U : Type v}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [AddCommGroup U] [Module ℝ U]
variable {P : Set E} {ψ : E → U → ℝ} {g : E → E}
variable (y : ∀ N : ℕ, Fin (N + 1) → E)
variable (u : ∀ N : ℕ, Fin (N + 1) → U)
variable (α : ∀ N : ℕ, Fin (N + 1) → ℝ)
variable (r : ℕ → ℝ)

local notation "hatf" =>
  fun N ↦ dotProduct (α N) (fun k ↦ ψ (y N k) (u N k))

local notation "uHat" =>
  fun N ↦ Finset.univ.centerMass (α N) (u N)

local notation "lowerValue" =>
  fun u' : U ↦ sInf ((fun x ↦ ψ x u') '' P)

local notation "gap" =>
  fun N ↦ hatf N - lowerValue (uHat N)

local notation "δ" =>
  fun N ↦ gapFunctionCertificate (y N) (α N) g

variable
    (hP_nonempty : P.Nonempty)
    (hlower_bddBelow :
      ∀ N : ℕ, BddBelow ((fun x ↦ ψ x ((Finset.univ).centerMass (α N) (u N))) '' P))
    (hα_nonneg : ∀ N : ℕ, ∀ k, 0 ≤ α N k)
    (hα_sum_one : ∀ N : ℕ, ∑ k, α N k = 1)
    (hsubgradient_uHat :
      ∀ N : ℕ, ∀ (k : Fin (N + 1)) (x : E) (_hx : x ∈ P),
        ψ (y N k) ((Finset.univ).centerMass (α N) (u N)) -
          ψ x ((Finset.univ).centerMass (α N) (u N)) ≤
            inner ℝ (g (y N k)) (y N k - x))
    (haggregate :
      ∀ N : ℕ,
        dotProduct (α N) (fun k ↦ ψ (y N k) (u N k)) ≤
          ∑ k, α N k * ψ (y N k) ((Finset.univ).centerMass (α N) (u N)))

include hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat haggregate

/-- Bridge theorem: the weighted primal-dual gap is bounded by the supremum of the certificate
image on `P`. This is the canonical `sSup` form of the source certificate estimate, before any
explicit residual sequence `r_N` is inserted. -/
-- Proof sketch: for fixed `N`, apply the affine minorant inequality with `u' = uHat N`, sum over
-- `k`, and use `hα_sum_one N` to rewrite the `x`-slice average as `ψ x (uHat N)`. The hypothesis
-- `hsubgradient_uHat` already supplies exactly that stagewise slice, and `haggregate` rewrites the
-- sampled dual term `hatf N` against the same `uHat N`, giving `hatf N - δ N x ≤ ψ x (uHat N)`
-- for every `x ∈ P`. Since the lower value is stated directly as
-- `sInf ((fun x ↦ ψ x (uHat N)) '' P)`, the only order side conditions needed are the localized
-- nonemptiness / bounded-below assumptions `hP_nonempty` and `hlower_bddBelow N`; taking the
-- infimum on the right and the supremum on the left yields the claimed bound.
theorem weightedPrimalDualGap_le_sSup_gapFunctionCertificate
    (hδ_bddAbove : ∀ N, BddAbove (δ N '' P)) :
    ∀ N,
      gap N ≤ sSup (δ N '' P) := by
  intro N
  have h_pointwise_gap_le : ∀ x ∈ P, hatf N - ψ x (uHat N) ≤ δ N x := by
    intro x hx
    have h_weighted_subgradient :
        ∑ k, α N k * (ψ (y N k) (uHat N) - ψ x (uHat N)) ≤
          ∑ k, α N k * inner ℝ (g (y N k)) (y N k - x) := by
      -- Sum the stagewise slice inequalities after multiplying by the nonnegative weights.
      simpa using
        Finset.sum_le_sum (fun k _hk ↦
          mul_le_mul_of_nonneg_left (hsubgradient_uHat N k x hx) (hα_nonneg N k))
    have h_rewrite_weighted_slice :
        ∑ k, α N k * (ψ (y N k) (uHat N) - ψ x (uHat N)) =
          (∑ k, α N k * ψ (y N k) (uHat N)) - ψ x (uHat N) := by
      -- Use `∑ α_k = 1` to collapse the weighted constant slice `ψ x (uHat N)`.
      calc
        ∑ k, α N k * (ψ (y N k) (uHat N) - ψ x (uHat N)) =
            ∑ k, (α N k * ψ (y N k) (uHat N) - α N k * ψ x (uHat N)) := by
              simp [mul_sub]
        _ = (∑ k, α N k * ψ (y N k) (uHat N)) - ∑ k, α N k * ψ x (uHat N) := by
              rw [Finset.sum_sub_distrib]
        _ = (∑ k, α N k * ψ (y N k) (uHat N)) - (∑ k, α N k) * ψ x (uHat N) := by
              rw [← Finset.sum_mul]
        _ = (∑ k, α N k * ψ (y N k) (uHat N)) - ψ x (uHat N) := by
              rw [hα_sum_one N, one_mul]
    have h_uHat_slice_le :
        (∑ k, α N k * ψ (y N k) (uHat N)) - ψ x (uHat N) ≤ δ N x := by
      -- Rewrite the certificate as the weighted inner-product sum and compare termwise.
      calc
        (∑ k, α N k * ψ (y N k) (uHat N)) - ψ x (uHat N) =
            ∑ k, α N k * (ψ (y N k) (uHat N) - ψ x (uHat N)) := by
              rw [h_rewrite_weighted_slice]
        _ ≤ ∑ k, α N k * inner ℝ (g (y N k)) (y N k - x) := h_weighted_subgradient
        _ = δ N x := by
              simpa using (gapFunctionCertificate_apply (y N) (α N) g x).symm
    -- Compare the original aggregate `hatf N` with the same `uHat N` slice average.
    exact (sub_le_sub_right (haggregate N) (ψ x (uHat N))).trans h_uHat_slice_le
  have h_lower_bound :
      hatf N - sSup (δ N '' P) ≤ lowerValue (uHat N) := by
    -- Show that `hatf N - sSup (δ N '' P)` is a lower bound for the whole feasible slice.
    refine le_csInf ?_ ?_
    · rcases hP_nonempty with ⟨x, hx⟩
      exact ⟨ψ x (uHat N), ⟨x, hx, rfl⟩⟩
    · intro b hb
      rcases hb with ⟨x, hx, rfl⟩
      have hδ_le_sup : δ N x ≤ sSup (δ N '' P) := by
        exact le_csSup (hδ_bddAbove N) ⟨x, hx, rfl⟩
      have h_gap_le_sup : hatf N - ψ x (uHat N) ≤ sSup (δ N '' P) := by
        exact (h_pointwise_gap_le x hx).trans hδ_le_sup
      linarith
  -- Rearranging the lower-bound inequality gives the canonical gap bound.
  linarith

/-- Bridge theorem from pointwise certificate control to the raw gap bound. This is not the main
source-facing statement of Lemma 3.24; it is the residual-bound corollary obtained by combining
the `sSup` bridge above with the pointwise estimate `δ_N(x) ≤ r_N`. -/
-- Proof sketch: the previous theorem gives
-- `gap N ≤ sSup (δ N '' P)`. The pointwise bound `hdelta`
-- makes `δ N '' P` bounded above by `r N`, while `hP_nonempty` supplies the needed nonempty
-- certificate image. Together these give the result by transitivity.
theorem weightedPrimalDualGap_le_of_gapFunctionCertificate_bound
    (hdelta :
      ∀ N (x : E), (_hx : x ∈ P) → δ N x ≤ r N) :
    ∀ N,
      gap N ≤ r N := by
  have hδ_bddAbove : ∀ N, BddAbove (δ N '' P) := by
    intro N
    refine ⟨r N, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hdelta N x hx
  have hδ_sup_le : ∀ N, sSup (δ N '' P) ≤ r N := by
    intro N
    refine csSup_le ?_ ?_
    · rcases hP_nonempty with ⟨x, hx⟩
      exact ⟨δ N x, ⟨x, hx, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hdelta N x hx
  intro N
  exact
    (weightedPrimalDualGap_le_sSup_gapFunctionCertificate
      y u α hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
      haggregate hδ_bddAbove N).trans
      (hδ_sup_le N)

section IntervalConsequences

variable (fStar φStar : ℝ)
variable
    (h_primal_lower :
      ∀ N : ℕ, fStar ≤ dotProduct (α N) (fun k ↦ ψ (y N k) (u N k)))
    (h_dual_upper_uHat :
      ∀ N : ℕ,
        sInf ((fun x ↦ ψ x ((Finset.univ).centerMass (α N) (u N))) '' P) ≤ φStar)
    (h_weak_duality : φStar ≤ fStar)

include h_primal_lower h_dual_upper_uHat h_weak_duality

local notation "decomposition" =>
  fun N ↦ (hatf N - fStar) + (φStar - lowerValue (uHat N))

/-- Lemma 3.24: if the weighted primal-dual gap is controlled by the attained certificate maximum
`max_{x ∈ P} δ_N(x)` and these maxima are bounded above by `r_N`, then for every stage `N` the
source decomposition
`(\hat f_N - f^*) + (\phi^* - inf_{x ∈ P} ψ(x, \hat u_N))`
with `\hat f_N = dotProduct (α N) (fun k ↦ ψ (y N k) (u N k))` and
`\hat u_N = (Finset.univ).centerMass (α N) (u N)` lies in the interval
`[0, \hat f_N - inf_{x ∈ P} ψ(x, \hat u_N)]`, and that gap is bounded above by `r_N`. -/
-- Proof sketch: the maximum-attainment hypothesis gives
-- `sSup (δ N '' P) = δMax N` via `(hδMax N).csSup_eq`, so the previous bridge theorem yields
-- `gap N ≤ δMax N`. With `hδMax_le N`, this becomes the raw
-- gap estimate by `r N`. The primal benchmark hypothesis and the stagewise lower-value upper bound
-- `h_dual_upper_uHat N` then let one apply the interval owner from `Lemma_3_1_24` directly,
-- since that owner now takes the local dual upper bound at `uHat N` as primitive input.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_max
    (δMax : ℕ → ℝ)
    (hδMax : ∀ N, IsGreatest (δ N '' P) (δMax N))
    (hδMax_le : ∀ N, δMax N ≤ r N) :
    ∀ N,
      decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  have hδ_bddAbove : ∀ N, BddAbove (δ N '' P) := by
    intro N
    refine ⟨δMax N, ?_⟩
    intro z hz
    exact (hδMax N).2 hz
  have h_gap_le_δMax : ∀ N, gap N ≤ δMax N := by
    intro N
    simpa [(hδMax N).csSup_eq] using
      (weightedPrimalDualGap_le_sSup_gapFunctionCertificate
        y u α hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
        haggregate hδ_bddAbove N)
  intro N
  -- Route correction: use the earlier interval owner from `Lemma_3_1_24`, with the certificate
  -- argument supplying the raw gap bound and the attained maximum only rewriting `sSup`.
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_max_delta
      (P := P) δ hatf lowerValue uHat fStar φStar r
      h_primal_lower h_dual_upper_uHat h_weak_duality
      δMax hδMax h_gap_le_δMax hδMax_le N)

/-- Companion `sSup` reformulation of Lemma 3.24. The source-facing statement above uses an
explicit attained maximum `δMax N`; this theorem keeps only the canonical supremum bound. -/
-- Proof sketch: combine `weightedPrimalDualGap_le_sSup_gapFunctionCertificate` with
-- `hδ_le N`, then apply the same stagewise interval-owner argument as in Lemma 3.24.
theorem primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_sSup
    (hδ_bddAbove : ∀ N, BddAbove (δ N '' P))
    (hδ_le : ∀ N, sSup (δ N '' P) ≤ r N) :
    ∀ N,
      decomposition N ∈ Set.Icc 0 (gap N) ∧ gap N ≤ r N := by
  intro N
  -- Delegate the interval conclusion to the canonical owner once the raw gap bound is known.
  simpa using
    (primal_dual_decomposition_mem_Icc_and_gap_le_of_gap_le_sSup_delta
      (P := P) δ hatf lowerValue uHat fStar φStar r
      h_primal_lower h_dual_upper_uHat h_weak_duality
      (weightedPrimalDualGap_le_sSup_gapFunctionCertificate
        y u α hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
        haggregate hδ_bddAbove)
      hδ_le N)

/-- Companion gap-only corollary of Lemma 3.24 under pointwise certificate control. -/
-- Proof sketch: apply
-- `primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_sSup`
-- using the supremum bound induced by `hdelta`, then read off `0 ≤ gap N ≤ r N`.
theorem weightedPrimalDualGap_nonneg_le_of_gapFunctionCertificate_bound
    (hdelta :
      ∀ N (x : E), (_hx : x ∈ P) → δ N x ≤ r N) :
    ∀ N,
      0 ≤ gap N ∧ gap N ≤ r N := by
  have hδ_bddAbove : ∀ N, BddAbove (δ N '' P) := by
    intro N
    refine ⟨r N, ?_⟩
    intro z hz
    rcases hz with ⟨x, hx, rfl⟩
    exact hdelta N x hx
  have hδ_le : ∀ N, sSup (δ N '' P) ≤ r N := by
    intro N
    refine csSup_le ?_ ?_
    · rcases hP_nonempty with ⟨x, hx⟩
      exact ⟨δ N x, ⟨x, hx, rfl⟩⟩
    · intro z hz
      rcases hz with ⟨x, hx, rfl⟩
      exact hdelta N x hx
  intro N
  have h_interval :=
    primal_dual_decomposition_mem_Icc_and_gap_le_of_gapFunctionCertificate_sSup
      y u α r hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
      haggregate fStar φStar h_primal_lower h_dual_upper_uHat h_weak_duality
      hδ_bddAbove hδ_le N
  have h_mem := Set.mem_Icc.mp h_interval.1
  refine ⟨?_, h_interval.2⟩
  exact le_trans h_mem.1 h_mem.2

/-- Companion convergence form under pointwise certificate control. -/
-- Proof sketch: the previous theorem gives
-- `0 ≤ gap N ≤ r N` for every `N`;
-- apply `squeeze_zero` together with `hr_tendsto`.
theorem weightedPrimalDualGap_tendsto_zero_of_gapFunctionCertificate_bound
    (hdelta :
      ∀ N (x : E), (_hx : x ∈ P) → δ N x ≤ r N)
    (hr_tendsto : Tendsto r atTop (nhds 0)) :
    Tendsto gap atTop (nhds 0) := by
  -- Reuse the interval theorem to get the stagewise squeeze `0 ≤ gap N ≤ r N`.
  have h_gap_nonneg : ∀ N, 0 ≤ gap N := by
    intro N
    exact
      (weightedPrimalDualGap_nonneg_le_of_gapFunctionCertificate_bound
        y u α r hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
        haggregate fStar φStar h_primal_lower h_dual_upper_uHat h_weak_duality
        hdelta N).1
  have h_gap_le : ∀ N, gap N ≤ r N := by
    intro N
    exact
      (weightedPrimalDualGap_nonneg_le_of_gapFunctionCertificate_bound
        y u α r hP_nonempty hlower_bddBelow hα_nonneg hα_sum_one hsubgradient_uHat
        haggregate fStar φStar h_primal_lower h_dual_upper_uHat h_weak_duality
        hdelta N).2
  exact squeeze_zero h_gap_nonneg h_gap_le hr_tendsto

end IntervalConsequences

end GapFunctionCertificateBound

end
