/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import Mathlib.Data.List.TFAE
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap03.Theorem_3_34
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Definition_6_48
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_49

-- Declarations for this item will be appended below by the statement pipeline.

open Filter
open scoped Topology InnerProductSpace Pointwise

universe u

namespace Set

section

variable {E : Type u} [AddCommGroup E] [Module ℝ E]

/-- Helper for Proposition 6.51: every natural point on the recession ray through a base point of
`C` remains in `C`. -/
lemma nat_ray_point_mem_of_mem_recessionCone {C : Set E} {x y : E} (hC_convex : Convex ℝ C)
    (hx : x ∈ rec C) (hy : y ∈ C) (n : ℕ) :
    ((n : ℝ) • x + y) ∈ C := by
  have hrec_cone : IsCone (rec C) := recessionCone_isCone hC_convex
  have hnx : (n : ℝ) • x ∈ rec C := by
    cases n with
    | zero =>
        simpa using zero_mem_recessionCone C
    | succ k =>
        have : ((Nat.succ k : ℕ) : ℝ) • x ∈ Set.Ioi (0 : ℝ) • rec C := by
          refine ⟨((Nat.succ k : ℕ) : ℝ), ?_, x, hx, by simp⟩
          change 0 < ((Nat.succ k : ℕ) : ℝ)
          exact_mod_cast Nat.succ_pos k
        simpa [hrec_cone.symm] using this
  have htranslate :=
    (mem_recessionCone_iff.1 hnx) (Set.mem_add.2 ⟨(n : ℝ) • x, by simp, y, hy, rfl⟩)
  simpa [add_comm] using htranslate

end

section

variable {𝓗 : Type u} [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗]

/-- Existence of a sequence in `C` and coefficients in `]0, 1]` tending to `0` whose scaled terms
converge strongly to `x`. -/
def HasStrongScaledApproximation (C : Set 𝓗) (x : 𝓗) : Prop :=
  ∃ xSeq : ℕ → C, ∃ α : ℕ → Set.Ioc (0 : ℝ) 1,
    Tendsto (fun n ↦ (α n : ℝ)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n ↦ (α n : ℝ) • (xSeq n : 𝓗)) atTop (𝓝 x)

/-- Existence of a sequence in `C` and coefficients in `]0, 1]` tending to `0` whose scaled terms
converge weakly to `x`. -/
def HasWeakScaledApproximation (C : Set 𝓗) (x : 𝓗) : Prop :=
  ∃ xSeq : ℕ → C, ∃ α : ℕ → Set.Ioc (0 : ℝ) 1,
    Tendsto (fun n ↦ (α n : ℝ)) atTop (𝓝 (0 : ℝ)) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ 𝓗 ((α n : ℝ) • (xSeq n : 𝓗))) atTop
        (𝓝 (toWeakSpace ℝ 𝓗 x))

/-- Helper for Proposition 6.51: the coefficients `1 / (n + 1)` belong to `]0, 1]`. -/
lemma inv_nat_add_one_mem_Ioc (n : ℕ) : (1 / (n + 1 : ℝ)) ∈ Set.Ioc (0 : ℝ) 1 := by
  constructor
  · -- Positivity of the reciprocal gives the left endpoint condition.
    positivity
  · -- The denominator is at least `1`, so its reciprocal is at most `1`.
    have hn : (1 : ℝ) ≤ (n + 1 : ℝ) := by
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    have hinv : 1 / (n + 1 : ℝ) ≤ 1 / (1 : ℝ) := by
      exact one_div_le_one_div_of_le (by norm_num) hn
    simpa using hinv

/-- Helper for Proposition 6.51: a recession direction yields the textbook strong scaled
approximation by the points `((n + 1) • x + y)` and coefficients `1 / (n + 1)`. -/
lemma hasStrongScaledApproximation_of_mem_recessionCone {C : Set 𝓗} {x : 𝓗}
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hx : x ∈ rec C) :
    HasStrongScaledApproximation C x := by
  rcases hC_nonempty with ⟨y, hy⟩
  have hxSeq_mem : ∀ n : ℕ, (((n + 1 : ℕ) : ℝ) • x + y) ∈ C := by
    -- Proposition 6.49 provides the ray points `(n + 1) • x + y` inside `C`.
    intro n
    exact nat_ray_point_mem_of_mem_recessionCone hC_convex hx hy (n + 1)
  have hα_tendsto : Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ))) atTop (𝓝 (0 : ℝ)) := by
    -- The explicit coefficients are the standard reciprocal tail.
    have hshift : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1)) atTop atTop := by
      exact tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop
    simpa [Nat.cast_add, one_div] using (tendsto_inv_atTop_zero.comp hshift)
  have hscaled_model :
      ∀ n : ℕ,
        (1 / (n + 1 : ℝ)) • ((((n + 1 : ℕ) : ℝ) • x) + y) =
          x + (1 / (n + 1 : ℝ)) • y := by
    intro n
    have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    -- The chosen scaling cancels the factor `(n + 1)` and leaves the remainder on `y`.
    calc
      (1 / (n + 1 : ℝ)) • ((((n + 1 : ℕ) : ℝ) • x) + y)
          = ((1 / (n + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ)) • x
              + (1 / (n + 1 : ℝ)) • y := by
                rw [smul_add, smul_smul]
      _ = x + (1 / (n + 1 : ℝ)) • y := by
        have hmul : (((n + 1 : ℕ) : ℝ)⁻¹ * ((n + 1 : ℕ) : ℝ)) = 1 := by
          field_simp [hne]
        have hfirst :
            ((1 / (n + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ)) • x = (1 : ℝ) • x := by
          exact congrArg (fun t : ℝ ↦ t • x) (by simpa [one_div] using hmul)
        calc
          ((1 / (n + 1 : ℝ)) * ((n + 1 : ℕ) : ℝ)) • x + (1 / (n + 1 : ℝ)) • y
              = (1 : ℝ) • x + (1 / (n + 1 : ℝ)) • y := by
                  rw [hfirst]
          _ = x + (1 / (n + 1 : ℝ)) • y := by
            simp
  let xSeq : ℕ → C := fun n ↦ ⟨(((n + 1 : ℕ) : ℝ) • x + y), hxSeq_mem n⟩
  let α : ℕ → Set.Ioc (0 : ℝ) 1 := fun n ↦ ⟨1 / (n + 1 : ℝ), inv_nat_add_one_mem_Ioc n⟩
  refine ⟨xSeq, α, ?_, ?_⟩
  · -- The scalar coefficients converge to `0`.
    simpa [α] using hα_tendsto
  · -- After rewriting the scaled model sequence, only the vanishing `y`-tail remains.
    have hscaled_y :
        Tendsto (fun n : ℕ ↦ (1 / (n + 1 : ℝ)) • y) atTop (𝓝 ((0 : ℝ) • y)) := by
      simpa using hα_tendsto.smul_const y
    have hsum :
        Tendsto (fun n : ℕ ↦ x + (1 / (n + 1 : ℝ)) • y) atTop
          (𝓝 (x + (0 : ℝ) • y)) := by
      exact tendsto_const_nhds.add hscaled_y
    have hseq_eq :
        (fun n : ℕ ↦ (α n : ℝ) • (xSeq n : 𝓗)) =
          fun n : ℕ ↦ x + (1 / (n + 1 : ℝ)) • y := by
      funext n
      simpa [xSeq, α] using hscaled_model n
    rw [hseq_eq]
    simpa using hsum

/-- Helper for Proposition 6.51: strong convergence immediately gives weak convergence after
transport through `toWeakSpaceCLM`. -/
lemma hasWeakScaledApproximation_of_hasStrongScaledApproximation {C : Set 𝓗} {x : 𝓗}
    (hApprox : HasStrongScaledApproximation C x) :
    HasWeakScaledApproximation C x := by
  rcases hApprox with ⟨xSeq, α, hα, hstrong⟩
  refine ⟨xSeq, α, hα, ?_⟩
  -- Compose the strong limit with the canonical continuous map to the weak space.
  simpa [toWeakSpaceCLM_eq_toWeakSpace] using
    (((toWeakSpaceCLM ℝ 𝓗).continuous.tendsto x).comp hstrong)

/-- Helper for Proposition 6.51: a weak scaled approximation forces every translate `x + y` with
`y ∈ C` back into `C`, hence `x ∈ rec C`. -/
lemma mem_recessionCone_of_hasWeakScaledApproximation {C : Set 𝓗} {x : 𝓗}
    (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) (hApprox : HasWeakScaledApproximation C x) :
    x ∈ rec C := by
  rcases hApprox with ⟨xSeq, α, hα, hweak⟩
  rw [mem_recessionCone_iff]
  intro z hz
  rcases Set.mem_add.1 hz with ⟨w, hw, y, hy, rfl⟩
  have hwx : w = x := by
    simpa using hw
  subst w
  let u : ℕ → 𝓗 := fun n ↦ (α n : ℝ) • (xSeq n : 𝓗) + (1 - (α n : ℝ)) • y
  have hu_mem : ∀ n : ℕ, u n ∈ C := by
    intro n
    have hα_nonneg : 0 ≤ (α n : ℝ) := (α n).2.1.le
    have hα_le_one : (α n : ℝ) ≤ 1 := (α n).2.2
    have hOneSub_nonneg : 0 ≤ 1 - (α n : ℝ) := by
      linarith
    -- Each `u n` is a convex combination of `xSeq n ∈ C` and the fixed base point `y ∈ C`.
    exact (convex_iff_add_mem.1 hC_convex) (xSeq n).property hy hα_nonneg hOneSub_nonneg
      (by ring)
  have hOneSub_tendsto : Tendsto (fun n : ℕ ↦ 1 - (α n : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    -- The complementary coefficients converge to `1`.
    simpa using (tendsto_const_nhds.sub hα)
  have hy_strong :
      Tendsto (fun n : ℕ ↦ (1 - (α n : ℝ)) • y) atTop (𝓝 ((1 : ℝ) • y)) := by
    -- Scaling a constant vector by coefficients tending to `1` converges strongly to `y`.
    simpa using hOneSub_tendsto.smul_const y
  have hy_weak :
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ 𝓗 ((1 - (α n : ℝ)) • y)) atTop
        (𝓝 (toWeakSpace ℝ 𝓗 y)) := by
    -- Strong convergence transports to weak convergence through `toWeakSpaceCLM`.
    simpa [toWeakSpaceCLM_eq_toWeakSpace] using
      (((toWeakSpaceCLM ℝ 𝓗).continuous.tendsto ((1 : ℝ) • y)).comp hy_strong)
  have hu_weak :
      Tendsto (fun n : ℕ ↦ toWeakSpace ℝ 𝓗 (u n)) atTop
        (𝓝 (toWeakSpace ℝ 𝓗 (x + y))) := by
    -- Adding the two weakly convergent pieces gives the target weak limit `x + y`.
    simpa [u, toWeakSpace] using hweak.add hy_weak
  -- Closed convexity now returns the weak limit of the sequence `u n ∈ C`.
  have hC_weakClosed : IsClosed ((toWeakSpace ℝ 𝓗) '' C) :=
    (isClosed_iff_weak_image_isClosed_of_convex hC_convex).1 hC_closed
  have hxyWeak :
      toWeakSpace ℝ 𝓗 (x + y) ∈ closure ((toWeakSpace ℝ 𝓗) '' C) := by
    exact mem_closure_of_tendsto hu_weak <|
      Filter.Eventually.of_forall fun n ↦ ⟨u n, hu_mem n, rfl⟩
  rw [hC_weakClosed.closure_eq] at hxyWeak
  rcases hxyWeak with ⟨v, hvC, hvEq⟩
  exact (toWeakSpace ℝ 𝓗).injective hvEq ▸ hvC

-- Proof sketch: Proposition 6.49 supplies the model sequence for `(i) → (ii)` by choosing
-- `αₙ = 1 / (n + 1)` and `xₙ = (n + 1) • x + y` with `y ∈ C`. The implication `(ii) → (iii)` is
-- immediate because norm convergence implies weak convergence. For `(iii) → (i)`, combine the weak
-- convergence of `αₙ • xₙ + (1 - αₙ) • y` with closed convexity and Corollary 3.35 to show
-- `x + y ∈ C` for every `y ∈ C`, hence `x ∈ rec C`.
/-- Proposition 6.51: for a nonempty closed convex set `C` and a vector `x`, membership of `x` in
`rec C` is equivalent to the existence of sequences `xₙ ∈ C` and `αₙ ∈ ]0, 1]` with `αₙ → 0`
such that `αₙ • xₙ → x` strongly, and also equivalent to the analogous weak convergence statement.
-/
theorem mem_recessionCone_tfae_exists_scaled_sequence_tendsto (C : Set 𝓗) (x : 𝓗)
    (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C) (hC_convex : Convex ℝ C) :
    List.TFAE
      [x ∈ rec C, HasStrongScaledApproximation C x, HasWeakScaledApproximation C x] := by
  -- The textbook proof is exactly the cycle `(i) → (ii) → (iii) → (i)`.
  tfae_have 1 → 2 := by
    intro hx
    -- Use the explicit recession-ray construction from Proposition 6.49.
    exact hasStrongScaledApproximation_of_mem_recessionCone hC_nonempty hC_convex hx
  tfae_have 2 → 3 := by
    intro hstrong
    -- Strong convergence is stronger than weak convergence after transport to `WeakSpace`.
    exact hasWeakScaledApproximation_of_hasStrongScaledApproximation hstrong
  tfae_have 3 → 1 := by
    intro hweak
    -- Closed convexity turns the weak limit of the convex-combination sequence back into `C`.
    exact mem_recessionCone_of_hasWeakScaledApproximation hC_closed hC_convex hweak
  tfae_finish

end

end Set
