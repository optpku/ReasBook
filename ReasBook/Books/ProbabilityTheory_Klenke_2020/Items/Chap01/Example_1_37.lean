/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Example_1_11
import Books.ProbabilityTheory_Klenke_2020.Items.Chap01.Definition_1_35

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory Set Filter
open scoped Classical ENNReal Topology

universe u

variable {Ω : Type u}

/- Example 1.37 uses the canonical finite-or-cofinite family from Example 1.11 and the canonical
`∅`-continuity predicate for additive contents from Definition 1.35. -/

/-- The set function used in the finite-cofinite example: finite sets get mass `0`, infinite sets
get mass `∞`. -/
private noncomputable def finiteCofiniteZeroInfiniteContentFun (Ω : Type u) (s : Set Ω) : ENNReal :=
  if s.Finite then (0 : ENNReal) else ∞

private theorem finiteCofiniteZeroInfiniteContentFun_apply (Ω : Type u) (s : Set Ω) :
    finiteCofiniteZeroInfiniteContentFun Ω s = if s.Finite then (0 : ENNReal) else ∞ :=
  rfl

private theorem finiteCofiniteZeroInfiniteContent_empty (Ω : Type u) :
    finiteCofiniteZeroInfiniteContentFun Ω ∅ = 0 := by
  simp [finiteCofiniteZeroInfiniteContentFun]

/-- Helper for Example 1.37: a decreasing sequence with empty intersection and one finite stage is
eventually empty. -/
private theorem eventually_eq_empty_of_antitone_iInter_eq_empty_of_finite
    {s : ℕ → Set Ω} (hanti : Antitone s) (hInter : (⋂ n, s n) = (∅ : Set Ω))
    {N : ℕ} (hfinite : (s N).Finite) :
    ∃ M, ∀ n ≥ M, s n = ∅ := by
  classical
  have hEventuallyNotMem : ∀ x ∈ s N, ∃ m ≥ N, x ∉ s m := by
    intro x hx
    by_contra hx'
    push Not at hx'
    have hxInter : x ∈ ⋂ n, s n := by
      refine mem_iInter.mpr ?_
      intro n
      by_cases hn : n < N
      · exact hanti (Nat.le_of_lt hn) hx
      · exact hx' n (le_of_not_gt hn)
    simp [hInter] at hxInter
  let witness : Ω → ℕ := fun x ↦
    if hx : x ∈ s N then Nat.find (hEventuallyNotMem x hx) else N
  let M := max N (hfinite.toFinset.sup witness)
  refine ⟨M, ?_⟩
  intro n hn
  ext x
  constructor
  · intro hx
    -- Any point in a sufficiently late set lies in the finite stage `s N`.
    have hNn : N ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hxN : x ∈ s N := hanti hNn hx
    have hxFinset : x ∈ hfinite.toFinset := by
      simpa using hxN
    have hw_le : witness x ≤ n := by
      exact le_trans (Finset.le_sup hxFinset) (le_trans (Nat.le_max_right _ _) hn)
    have hxWitnessNot : x ∉ s (witness x) := by
      rw [show witness x = Nat.find (hEventuallyNotMem x hxN) by simp [witness, hxN]]
      exact (Nat.find_spec (hEventuallyNotMem x hxN)).2
    exact (hxWitnessNot (hanti hw_le hx)).elim
  · simp

/-- Helper for Example 1.37: a surjective enumeration covers the space by its singleton fibers. -/
private theorem iUnion_singleton_eq_univ_of_surjective (g : ℕ → Ω)
    (hsurj : Function.Surjective g) :
    (⋃ n, ({g n} : Set Ω)) = Set.univ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    rcases hsurj x with ⟨n, rfl⟩
    exact mem_iUnion.mpr ⟨n, by simp⟩

-- Proof sketch: if the finite disjoint union is finite, then every summand is finite and both sides
-- are `0`; if the union is cofinite, one of the summands is cofinite and forces both sides to be
-- `∞`.
private theorem finiteCofiniteZeroInfiniteContent_sUnion (Ω : Type u) (I : Finset (Set Ω))
    (hI : ↑I ⊆ finiteOrCofiniteFamily Ω)
    (hdis : PairwiseDisjoint (I : Set (Set Ω)) id)
    (hmem : ⋃₀ ↑I ∈ finiteOrCofiniteFamily Ω) :
    finiteCofiniteZeroInfiniteContentFun Ω (⋃₀ ↑I) =
      ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u := by
  classical
  set U : Set Ω := ⋃₀ (↑I : Set (Set Ω))
  by_cases hfinite : U.Finite
  · -- If the union is finite, every summand is finite as a subset of that union.
    have hSummandFinite : ∀ u ∈ I, u.Finite := by
      intro u hu
      refine hfinite.subset ?_
      simpa [U] using (subset_sUnion_of_mem hu : u ⊆ ⋃₀ (↑I : Set (Set Ω)))
    have hsum_zero :
        ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u = 0 := by
      refine Finset.sum_eq_zero ?_
      intro u hu
      simp [finiteCofiniteZeroInfiniteContentFun, hSummandFinite u hu]
    calc
      finiteCofiniteZeroInfiniteContentFun Ω U = 0 := by
        simp [finiteCofiniteZeroInfiniteContentFun, hfinite]
      _ = ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u := hsum_zero.symm
  · -- If the union is infinite but still finite-or-cofinite, its complement is finite.
    have hUnionCofinite : Uᶜ.Finite := by
      simpa [finiteOrCofiniteFamily, hfinite] using hmem
    have hUnionFiniteOfAllFinite :
        ∀ {J : Finset (Set Ω)}, (∀ u ∈ J, u.Finite) → (⋃₀ (↑J : Set (Set Ω))).Finite := by
      intro J hAllFinite
      induction J using Finset.induction with
      | empty =>
          simp
      | insert u J huJ ih =>
          have huFinite : u.Finite := hAllFinite u (by simp)
          have hJFinite : (⋃₀ (↑J : Set (Set Ω))).Finite := by
            apply ih
            intro t ht
            exact hAllFinite t (by simp [ht])
          simpa [Finset.coe_insert, Set.sUnion_insert] using huFinite.union hJFinite
    have hNotAllFinite : ¬ ∀ u ∈ I, u.Finite := by
      intro hAllFinite
      exact hfinite (hUnionFiniteOfAllFinite hAllFinite)
    have hExistsInfinite : ∃ u ∈ I, ¬ u.Finite := by
      by_contra h
      exact hNotAllFinite <| by
        intro u hu
        by_contra hu_not_finite
        exact h ⟨u, hu, hu_not_finite⟩
    rcases hExistsInfinite with ⟨u0, hu0, hu0_not_finite⟩
    have hu0ComplFinite : u0ᶜ.Finite := by
      simpa [finiteOrCofiniteFamily, hu0_not_finite] using hI hu0
    have hOtherFinite : ∀ u ∈ I, u ≠ u0 → u.Finite := by
      intro u hu hne
      have hdisjoint : ∀ ⦃x : Ω⦄, x ∈ u → x ∈ u0 → False := by
        simpa [Set.disjoint_left] using hdis hu hu0 hne
      refine hu0ComplFinite.subset ?_
      intro x hx
      rw [Set.mem_compl_iff]
      exact fun hxu0 ↦ hdisjoint hx hxu0
    have hsum_eq_top :
        ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u = ∞ := by
      rw [Finset.sum_eq_single_of_mem u0 hu0]
      · simp [finiteCofiniteZeroInfiniteContentFun, hu0_not_finite]
      · intro u hu hne
        simp [finiteCofiniteZeroInfiniteContentFun, hOtherFinite u hu hne]
    calc
      finiteCofiniteZeroInfiniteContentFun Ω U = ∞ := by
        simp [finiteCofiniteZeroInfiniteContentFun, hfinite]
      _ = ∑ u ∈ I, finiteCofiniteZeroInfiniteContentFun Ω u := hsum_eq_top.symm

/-- The content on the finite-or-cofinite family that assigns `0` to finite sets and `∞` to
infinite sets. -/
noncomputable def finiteCofiniteZeroInfiniteContent (Ω : Type u) :
    AddContent ENNReal (finiteOrCofiniteFamily Ω) where
  toFun := finiteCofiniteZeroInfiniteContentFun Ω
  empty' := finiteCofiniteZeroInfiniteContent_empty Ω
  sUnion' := finiteCofiniteZeroInfiniteContent_sUnion Ω

/-- The bundled finite-or-cofinite content is given by the stated zero-or-infinity formula. -/
@[simp] theorem finiteCofiniteZeroInfiniteContent_apply (Ω : Type u) (s : Set Ω) :
    finiteCofiniteZeroInfiniteContent Ω s = if s.Finite then (0 : ENNReal) else ∞ := by
  exact finiteCofiniteZeroInfiniteContentFun_apply Ω s

-- Proof sketch: for a decreasing sequence in the finite-or-cofinite family with empty
-- intersection, countability lets one exhaust the remaining points and show that all sufficiently
-- late terms are finite, hence the values are eventually `0` and converge to `0`.
/-- The finite-or-cofinite content is `∅`-continuous on a countably infinite ambient set. -/
instance finiteCofiniteZeroInfiniteContent_isContinuousAtEmpty (Ω : Type u) [Countable Ω]
    [Infinite Ω] :
    AddContent.IsContinuousAtEmpty (finiteCofiniteZeroInfiniteContent Ω) := by
  refine ⟨?_⟩
  intro s hs hdecr hfin
  rcases hfin with ⟨N, hN⟩
  -- A finite value can only occur on a finite set because the content takes values `0` and `∞`.
  have hsNFinite : (s N).Finite := by
    by_contra hsN_not_finite
    simp [finiteCofiniteZeroInfiniteContent_apply, hsN_not_finite] at hN
  -- Once the decreasing tail is eventually empty, the content sequence is eventually constant `0`.
  obtain ⟨M, hM⟩ :=
    eventually_eq_empty_of_antitone_iInter_eq_empty_of_finite
      hdecr.antitone hdecr.iInter_eq hsNFinite
  have hEventuallyZero :
      (finiteCofiniteZeroInfiniteContent Ω ∘ s) =ᶠ[atTop] fun _ ↦ (0 : ENNReal) := by
    refine Filter.eventually_atTop.2 ⟨M, ?_⟩
    intro n hn
    rw [Function.comp_apply, hM n hn, finiteCofiniteZeroInfiniteContent_apply]
    simp
  exact Tendsto.congr' hEventuallyZero.symm tendsto_const_nhds

-- Proof sketch: apply σ-subadditivity to a partition of the countably infinite ambient space into
-- singletons; the left-hand side is `∞` while the right-hand side is `0`.
/-- The finite-or-cofinite content is not σ-subadditive on a countably infinite ambient set. -/
theorem finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive (Ω : Type u) [Countable Ω]
    [Infinite Ω] :
    ¬ (finiteCofiniteZeroInfiniteContent Ω).IsSigmaSubadditive := by
  intro hsub
  obtain ⟨g, hsurj⟩ := exists_surjective_nat Ω
  let f : ℕ → Set Ω := fun n ↦ {g n}
  have hf : ∀ n, f n ∈ finiteOrCofiniteFamily Ω := by
    intro n
    simp [f, finiteOrCofiniteFamily]
  have hUnion_eq : (⋃ n, f n) = Set.univ := by
    simpa [f] using iUnion_singleton_eq_univ_of_surjective (Ω := Ω) g hsurj
  have hUnion_mem : (⋃ n, f n) ∈ finiteOrCofiniteFamily Ω := by
    rw [hUnion_eq]
    simp [finiteOrCofiniteFamily]
  have hineq := hsub hf hUnion_mem
  -- Route correction: use the zero-on-singletons and infinity-on-`univ` formulas directly.
  have huniv_value : finiteCofiniteZeroInfiniteContent Ω Set.univ = ∞ := by
    have huniv_not_finite : ¬ (Set.univ : Set Ω).Finite := by
      simpa using (Set.infinite_univ : (Set.univ : Set Ω).Infinite)
    simp [finiteCofiniteZeroInfiniteContent_apply, huniv_not_finite]
  have hsingleton_value : ∀ n, finiteCofiniteZeroInfiniteContent Ω (f n) = 0 := by
    intro n
    rw [finiteCofiniteZeroInfiniteContent_apply]
    simp [f]
  have htsum_zero : ∑' n, finiteCofiniteZeroInfiniteContent Ω (f n) = 0 := by
    calc
      ∑' n, finiteCofiniteZeroInfiniteContent Ω (f n) = ∑' n, (0 : ENNReal) := by
        refine tsum_congr hsingleton_value
      _ = 0 := tsum_zero
  rw [hUnion_eq, huniv_value, htsum_zero] at hineq
  exact (not_le_of_gt (by simp : (0 : ENNReal) < ∞)) hineq

/-- Example 1.37: On a countably infinite set, the content assigning mass `0` to finite sets and
mass `∞` to infinite sets is `∅`-continuous and fails the canonical premeasure predicate
`AddContent.IsSigmaSubadditive`. -/
theorem finiteCofiniteZeroInfiniteContent_continuousAtEmpty_not_premeasure (Ω : Type u)
    [Countable Ω] [Infinite Ω] :
    AddContent.IsContinuousAtEmpty (finiteCofiniteZeroInfiniteContent Ω) ∧
      ¬ (finiteCofiniteZeroInfiniteContent Ω).IsSigmaSubadditive := by
  exact ⟨inferInstance,
    finiteCofiniteZeroInfiniteContent_not_isSigmaSubadditive Ω⟩
