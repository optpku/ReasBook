/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Lemma_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_11
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open InnerProductSpace (toDualMap)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- Proposition 4.3 is `source-facing`: it identifies the conjugate of the support function with
the indicator of the closed convex hull. The owner abstractions already live upstream:
the indicator notation `δ_ C` in Chapter 2, the primal support-function owner `σ[C]`
in Chapter 2, and
Definition 4.1's owner pair `conjugate_function` / `conjugate_function_primal`. This file
therefore keeps only the proposition itself. -/
recall conjugate_function_primal

-- Semantic recall: `lean_leansearch` surfaced only general closed-convex-hull API, not a
-- project-specific owner theorem for this exact conjugacy identity, so this file keeps the
-- faithful source-facing statement directly on the chapter owners `σ[C]` and `f∗`.
-- Proof sketch: combine Proposition 4.1 with the Chapter 2 support-function invariance under
-- convex hull and closure, then use the finite-dimensional Euclidean biconjugation setup from the
-- surrounding Chapter 4 results.
/-- Helper for Proposition 4.3: replacing a set by its closure does not change the primal support
function `σ[C]`. -/
lemma supportFunctionPrimal_eq_closure (C : Set E) :
    σ[C] = σ[closure C] := by
  -- Compare both support functions through the same `sSup` formula of inner products.
  ext x
  rw [support_function_eq_sSup, support_function_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- The closure contains the original set, so its supremum is at least as large.
    refine sSup_le ?_
    rintro _ ⟨y, hyC, rfl⟩
    exact le_sSup ⟨y, subset_closure hyC, rfl⟩
  · -- Continuity of `z ↦ ⟪x, z⟫` transfers the supremum bound back to the closure.
    refine sSup_le ?_
    rintro _ ⟨y, hyC, rfl⟩
    let f : E → EReal := fun z ↦ (inner ℝ x z : EReal)
    have hf_cont : Continuous f := by
      simpa [f, InnerProductSpace.toDualMap_apply_apply] using
        (continuous_coe_real_ereal.comp (toDualMap ℝ E x).continuous)
    have hsubset : f '' C ⊆ Set.Iic (sSup (f '' C)) := by
      rintro _ ⟨z, hzC, rfl⟩
      exact le_sSup (Set.mem_image_of_mem f hzC)
    have hclosure :
        closure (f '' C) ⊆ Set.Iic (sSup (f '' C)) :=
      closure_minimal hsubset isClosed_Iic
    have hy_mem : f y ∈ closure (f '' C) :=
      (image_closure_subset_closure_image hf_cont) ⟨y, hyC, rfl⟩
    exact hclosure hy_mem

/-- Helper for Proposition 4.3: replacing a set by its convex hull does not change the primal
support function `σ[C]`. -/
lemma supportFunctionPrimal_eq_convexHull (C : Set E) :
    σ[C] = σ[convexHull ℝ C] := by
  -- Compare both support functions through the same `sSup` formula of inner products.
  ext x
  rw [support_function_eq_sSup, support_function_eq_sSup]
  refine le_antisymm ?_ ?_
  · -- The convex hull contains the original set, so its supremum is at least as large.
    refine sSup_le ?_
    rintro _ ⟨y, hyC, rfl⟩
    exact le_sSup ⟨y, subset_convexHull ℝ C hyC, rfl⟩
  · -- A linear functional has the same supremum on a set and on its convex hull.
    refine sSup_le ?_
    rintro _ ⟨y, hyC, rfl⟩
    have hconv :
        ConvexOn ℝ (Set.univ : Set E) (fun z : E ↦ inner ℝ x z) := by
      simpa [InnerProductSpace.toDualMap_apply_apply] using
        LinearMap.convexOn (toDualMap ℝ E x).toLinearMap
          (convex_univ : Convex ℝ (Set.univ : Set E))
    obtain ⟨z, hzC, hzmax⟩ :=
      hconv.exists_ge_of_mem_convexHull (Set.subset_univ C) hyC
    exact
      (show (inner ℝ x y : EReal) ≤ (inner ℝ x z : EReal) from by
        exact_mod_cast hzmax).trans <|
        le_sSup ⟨z, hzC, rfl⟩

/-- Helper for Proposition 4.3: the primal support function depends only on
`closure (convexHull ℝ C)`. -/
lemma supportFunctionPrimal_eq_closureConvexHull (C : Set E) :
    σ[C] = σ[closure (convexHull ℝ C)] := by
  -- Normalize first by convexification and then by closure.
  calc
    σ[C] = σ[convexHull ℝ C] := supportFunctionPrimal_eq_convexHull C
    _ = σ[closure (convexHull ℝ C)] := supportFunctionPrimal_eq_closure (convexHull ℝ C)

/-- Helper for Proposition 4.3: if every pairing `⟪u, k⟫` with `k ∈ K` is bounded above by `α`,
then the support function of `K` at `u` is also bounded above by `α`. -/
lemma supportFunctionPrimal_le_of_forall_inner_le
    (K : Set E) (u : E) (α : ℝ) (hK : ∀ k ∈ K, inner ℝ u k ≤ α) :
    σ[K] u ≤ (α : EReal) := by
  -- Rewrite the support function as a supremum and bound each element of the image.
  rw [support_function_eq_sSup]
  refine sSup_le ?_
  rintro _ ⟨k, hk, rfl⟩
  have hk' : (((inner ℝ u k : ℝ) : EReal)) ≤ (α : EReal) := by
    exact_mod_cast hK k hk
  exact hk'

/-- Helper for Proposition 4.3: on a point `y ∈ K`, the conjugate of the support function of `K`
vanishes. -/
lemma conjugateSupportFunction_eq_zero_of_mem
    (K : Set E) {y : E} (hy : y ∈ K) :
    (σ[K]∗) y = 0 := by
  -- Expand the conjugate and show each term in the defining supremum is at most `0`.
  rw [conjugate_function_primal_apply, conjugate_function_apply]
  apply le_antisymm
  · refine sSup_le ?_
    rintro _ ⟨z, rfl⟩
    have hz_le : (((toDualMap ℝ E y) z : ℝ) : EReal) ≤ σ[K] z := by
      simpa [support_function_primal_apply, InnerProductSpace.toDualMap_apply_apply,
        real_inner_comm]
        using le_support_function_of_mem hy (toDualMap ℝ E z)
    exact (show ((((toDualMap ℝ E y) z : ℝ) : EReal) - σ[K] z) ≤ 0 from
      EReal.sub_nonpos.mpr hz_le)
  · -- Evaluating the defining supremum at `z = 0` gives the reverse inequality.
    have hσzero_le : σ[K] (0 : E) ≤ (0 : EReal) :=
      supportFunctionPrimal_le_of_forall_inner_le K 0 0 (by
        intro k hk
        simp)
    have hσzero_ge : (0 : EReal) ≤ σ[K] (0 : E) := by
      simpa [support_function_primal_apply, InnerProductSpace.toDualMap_apply_apply] using
        le_support_function_of_mem hy (toDualMap ℝ E (0 : E))
    have hσzero : σ[K] (0 : E) = 0 :=
      le_antisymm hσzero_le hσzero_ge
    refine le_sSup ?_
    refine Set.mem_range.mpr ⟨(0 : E), ?_⟩
    rw [hσzero]
    simp [InnerProductSpace.toDualMap_apply_apply]

/-- Helper for Proposition 4.3: outside a closed convex set `K`, the conjugate of the support
function of `K` is `⊤`. -/
lemma conjugateSupportFunction_eq_top_of_not_mem
    (K : Set E) (hK_closed : IsClosed K) (hK_convex : Convex ℝ K) {y : E} (hy : y ∉ K) :
    (σ[K]∗) y = ⊤ := by
  rcases Set.eq_empty_or_nonempty K with hK_empty | hK_nonempty
  · -- If `K` is empty, then the support function is `⊥`, so every conjugate integrand is `⊤`.
    rw [hK_empty, conjugate_function_primal_apply, conjugate_function_apply]
    refine (sSup_eq_top).2 ?_
    intro b hb
    refine ⟨⊤, Set.mem_range.mpr ⟨(0 : E), ?_⟩, hb⟩
    simp [support_function_apply]
  · -- Otherwise, strict separation supplies a direction along which the conjugate grows to `⊤`.
    obtain ⟨p, hp_ne_zero, α, hpy, hpK⟩ :=
      strict_separation_closed_convex_point hK_nonempty hK_closed hK_convex hy
    rcases (InnerProductSpace.toDual ℝ E).surjective p with ⟨u, hu⟩
    have hu_apply (x : E) : p x = inner ℝ u x := by
      simpa [InnerProductSpace.toDual_apply_apply] using
        (congrArg (fun ψ : StrongDual ℝ E ↦ ψ x) hu).symm
    have hK_bound : ∀ k ∈ K, inner ℝ u k ≤ α := by
      intro k hk
      simpa [hu_apply k] using hpK k hk
    have hgap : 0 < inner ℝ y u - α := by
      have hpy' : inner ℝ y u > α := by
        simpa [hu_apply y, real_inner_comm] using hpy
      linarith
    rw [conjugate_function_primal_apply, conjugate_function_apply]
    refine (sSup_eq_top).2 ?_
    intro b hb
    rcases EReal.lt_iff_exists_real_btwn.1 hb with ⟨r, hbr, _⟩
    let δ : ℝ := inner ℝ y u - α
    have hδ : 0 < δ := by
      simpa [δ] using hgap
    obtain ⟨n, hn⟩ := exists_nat_gt (r / δ)
    have hr_lt_scaled : r < (n : ℝ) * δ := by
      have hn' : r / δ < (n : ℝ) := by
        exact_mod_cast hn
      exact (_root_.div_lt_iff₀ hδ).1 hn'
    have hsupport_scaled :
        σ[K] ((n : ℝ) • u) ≤ ((((n : ℝ) * α : ℝ)) : EReal) := by
      refine supportFunctionPrimal_le_of_forall_inner_le K ((n : ℝ) • u) ((n : ℝ) * α) ?_
      intro k hk
      have hn_nonneg : 0 ≤ (n : ℝ) := by
        exact_mod_cast Nat.zero_le n
      simpa [real_inner_smul_left] using mul_le_mul_of_nonneg_left (hK_bound k hk) hn_nonneg
    have hpair_scaled :
        (((toDualMap ℝ E y) ((n : ℝ) • u) : ℝ) : EReal) =
          ((((n : ℝ) * inner ℝ y u : ℝ)) : EReal) := by
      rw [InnerProductSpace.toDualMap_apply_apply, real_inner_smul_right]
    have hlower :
        ((((n : ℝ) * δ : ℝ)) : EReal) ≤
          (((toDualMap ℝ E y) ((n : ℝ) • u) : ℝ) : EReal) - σ[K] ((n : ℝ) • u) := by
      calc
        ((((n : ℝ) * δ : ℝ)) : EReal)
            = ((((n : ℝ) * inner ℝ y u : ℝ)) : EReal) -
                ((((n : ℝ) * α : ℝ)) : EReal) := by
                  rw [show (n : ℝ) * δ = (n : ℝ) * inner ℝ y u - (n : ℝ) * α by
                    simp [δ, mul_sub]]
                  rw [EReal.coe_sub]
        _ ≤ ((((n : ℝ) * inner ℝ y u : ℝ)) : EReal) - σ[K] ((n : ℝ) • u) := by
              exact EReal.sub_le_sub le_rfl hsupport_scaled
        _ = (((toDualMap ℝ E y) ((n : ℝ) • u) : ℝ) : EReal) - σ[K] ((n : ℝ) • u) := by
              rw [hpair_scaled]
    refine ⟨_, Set.mem_range.mpr ⟨(n : ℝ) • u, rfl⟩, ?_⟩
    calc
      b < (r : EReal) := hbr
      _ < ((((n : ℝ) * δ : ℝ)) : EReal) := by
            exact_mod_cast hr_lt_scaled
      _ ≤ (((toDualMap ℝ E y) ((n : ℝ) • u) : ℝ) : EReal) - σ[K] ((n : ℝ) • u) := hlower

/-- Proposition 4.3: the Fenchel conjugate of the primal support function `σ[C]` is
`δ_ (closure (convexHull ℝ C))`. The textbook states this for nonempty `C`, but
the same identity remains valid for arbitrary `C`. -/
theorem conjugate_function_support_function_eq_extendedIndicator_closure_convexHull
    (C : Set E) :
    (σ[C]∗) = δ_ (closure (convexHull ℝ C)) := by
  let K : Set E := closure (convexHull ℝ C)
  have hσ : σ[C] = σ[K] := by
    simpa [K] using supportFunctionPrimal_eq_closureConvexHull C
  have hconj : (σ[C]∗) = (σ[K]∗) :=
    congrArg conjugate_function_primal hσ
  have hK_closed : IsClosed K := by
    simpa [K] using isClosed_closure
  have hK_convex : Convex ℝ K := by
    simpa [K] using (convex_convexHull ℝ C).closure
  ext y
  have hpoint : (σ[C]∗) y = (σ[K]∗) y := by
    simpa using congrArg (fun f : E → EReal ↦ f y) hconj
  by_cases hy : y ∈ K
  · -- On `K`, the conjugate branch equals `0`, exactly like the indicator.
    calc
      (σ[C]∗) y = (σ[K]∗) y := hpoint
      _ = 0 := conjugateSupportFunction_eq_zero_of_mem K hy
      _ = (δ_ K) y := by simpa using (extendedIndicator_of_mem hy).symm
  · -- Outside `K`, strict separation forces the conjugate branch to be `⊤`.
    calc
      (σ[C]∗) y = (σ[K]∗) y := hpoint
      _ = ⊤ := conjugateSupportFunction_eq_top_of_not_mem K hK_closed hK_convex hy
      _ = (δ_ K) y := by simpa using (extendedIndicator_of_not_mem hy).symm

/-- Pointwise form of Proposition 4.3. -/
@[simp] theorem conjugate_function_support_function_apply_eq_extendedIndicator_closure_convexHull
    (C : Set E) (x : E) :
    (σ[C]∗) x = (δ_ (closure (convexHull ℝ C))) x := by
  simpa using
    congrFun (conjugate_function_support_function_eq_extendedIndicator_closure_convexHull C) x

end
