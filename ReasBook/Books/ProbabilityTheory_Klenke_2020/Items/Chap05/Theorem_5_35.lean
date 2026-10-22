/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib
import Books.ProbabilityTheory_Klenke_2020.Items.Chap02.Definition_2_14

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory
open scoped BigOperators ProbabilityTheory unitInterval

universe u

variable {Ω : Type u} [MeasurableSpace Ω]

-- Local multinomial-count API copied into this file so the proof does not depend on the
-- currently broken Chapter 2 item module.
namespace Theorem535Local

variable {m n : ℕ}

/-- Helper for Theorem 5.35: `multinomialCount X ω i` counts how many coordinates of the
finite sample `X 0 ω, …, X (n - 1) ω` are equal to `i`. -/
def multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) : Fin m → ℕ :=
  fun i ↦ Finset.card <| Finset.univ.filter fun j ↦ X j ω = i

section

omit [MeasurableSpace Ω]

/-- Helper for Theorem 5.35: the entries of the multinomial count vector sum to the sample
size `n`. -/
theorem sum_multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) :
    ∑ i, multinomialCount X ω i = n := by
  let f : Fin n → Fin m := fun j ↦ X j ω
  have h_mapsTo :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).MapsTo f (Finset.univ : Finset (Fin m)) :=
    fun _ _ ↦ Finset.mem_univ _
  simpa [multinomialCount] using
    (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm

end

section

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Theorem 5.35: `tupleCount x` is the deterministic histogram of a finite word
`x : Fin n → Fin m`. -/
private def tupleCount (x : Fin n → Fin m) : Fin m → ℕ :=
  multinomialCount (fun j ↦ fun y : Fin n → Fin m ↦ y j) x

/-- Helper for Theorem 5.35: the deterministic histogram of a word agrees with the multiplicity
function of its associated list. -/
private theorem tupleCount_eq_listCount (x : Fin n → Fin m) (i : Fin m) :
    tupleCount x i = (List.ofFn x).count i := by
  -- Proof comment: rewrite the histogram as a cardinality of coordinate fibers, then use the
  -- standard `Fin` lemma relating that cardinality to the count of `i` in the word list.
  simpa [tupleCount, multinomialCount] using
    Fin.card_filter_univ_eq_vector_get_eq_count i (List.Vector.ofFn x)

/-- Helper for Theorem 5.35: the joint law of the sampled word is the finite product measure of
the common marginal law `p`. -/
private theorem sampleVecMap_eq_productMeasure
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) :
    μ.map (fun ω i ↦ X i ω) = Measure.pi (fun _ : Fin n ↦ p.toMeasure) := by
  -- Proof comment: independence identifies the pushforward joint law with the product of the
  -- coordinate laws, and the common-law assumption replaces every marginal by `p.toMeasure`.
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun i ↦ (h_law i).aemeasurable).1 h_indep]
  congr 1
  funext i
  exact (h_law i).map_eq

/-- Helper for Theorem 5.35: a single word has the expected iid product mass. -/
private theorem sampleVecPointMass_eq_prod
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (x : Fin n → Fin m) :
    μ.map (fun ω i ↦ X i ω) ({x} : Set (Fin n → Fin m)) = ∏ j, p (x j) := by
  -- Proof comment: evaluate the pushforward measure on the singleton `{x}` and use the product
  -- measure formula for singleton rectangles.
  rw [sampleVecMap_eq_productMeasure p X h_indep h_law, Measure.pi_singleton]
  simp

/-- Helper for Theorem 5.35: if a word has histogram `k`, then its iid product weight depends
only on `k`. -/
private theorem sampleWordWeight_eq_prodPow_of_tupleCount_eq
    (p : PMF (Fin m)) (x : Fin n → Fin m) (k : Fin m → ℕ) (hx : tupleCount x = k) :
    ∏ j, p (x j) = ∏ i, (p i) ^ k i := by
  -- Proof comment: rewrite the word weight as the product over the multiset of letters, then
  -- group equal letters together and replace their multiplicities by the prescribed histogram `k`.
  have hcount : ∀ i, (List.ofFn x).count i = k i := by
    intro i
    rw [← tupleCount_eq_listCount x i, hx]
  calc
    ∏ j, p (x j) = (List.ofFn fun j ↦ p (x j)).prod := by
      simpa using (Fin.prod_ofFn fun j ↦ p (x j)).symm
    _ = ((List.ofFn x).map p).prod := by
      congr
      apply List.ext_getElem <;> simp [List.length_ofFn, List.getElem_ofFn]
    _ = ∏ i ∈ (List.ofFn x).toFinset, p i ^ (List.ofFn x).count i := by
      simpa using (Finset.prod_multiset_map_count (List.ofFn x : Multiset (Fin m)) p)
    _ = ∏ i, p i ^ (List.ofFn x).count i := by
      refine Finset.prod_subset (by simp) ?_
      intro i _ hi
      have hi' : i ∉ List.ofFn x := by
        simpa using hi
      simp [List.count_eq_zero_of_not_mem hi']
    _ = ∏ i, (p i) ^ k i := by
      refine Finset.prod_congr rfl ?_
      intro i _
      rw [hcount i]

/-- Helper for Theorem 5.35: every admissible count vector is realized by at least one word of
length `n`. -/
private theorem exists_word_with_tupleCount (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    ∃ x : Fin n → Fin m, tupleCount x = k := by
  classical
  let s : Sym (Fin m) n := (Sym.equivNatSumOfFintype (Fin m) n).symm ⟨k, hk⟩
  let v : List.Vector (Fin m) n :=
    ⟨(s : Multiset (Fin m)).toList, by simp [Sym.card_coe]⟩
  refine ⟨v.get, ?_⟩
  ext i
  -- Proof comment: choose the canonical list representative of the symmetric word attached to
  -- `k`; its multiplicity function is exactly `k`.
  calc
    tupleCount v.get i = (List.ofFn v.get).count i := tupleCount_eq_listCount v.get i
    _ = v.toList.count i := by
      have hlist : List.ofFn v.get = v.toList := by
        exact (List.Vector.toList_ofFn v.get).symm.trans
          (congrArg Subtype.val (List.Vector.ofFn_get v))
      exact congrArg (List.count i) hlist
    _ = (s : Multiset (Fin m)).count i := by
      rw [show v.toList = (s : Multiset (Fin m)).toList by rfl]
      rw [← Multiset.coe_count]
      exact congrArg (Multiset.count i) (Multiset.coe_toList (s : Multiset (Fin m)))
    _ = k i := by
      simpa [s] using
        (Sym.coe_equivNatSumOfFintype_apply_apply (α := Fin m) (n := n) s i).symm

/-- Helper for Theorem 5.35: the type synonym `((Equiv.Perm (Fin n))ᵈᵐᵃ)` is finite because it
is equivalent to `Equiv.Perm (Fin n)`. -/
private instance fintypeDomMulActPermFin : Fintype ((Equiv.Perm (Fin n))ᵈᵐᵃ) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n)) DomMulAct.mk

/-- Helper for Theorem 5.35: the histogram entry `tupleCount x i` is the cardinality of the
fiber `{j // x j = i}`. -/
private theorem fintypeCard_fiber_eq_tupleCount (x : Fin n → Fin m) (i : Fin m) :
    Fintype.card {j // x j = i} = tupleCount x i := by
  -- Proof comment: identify the fiber subtype with the filtered universal finset used in the
  -- definition of `tupleCount`.
  rw [Fintype.card_of_subtype (s := Finset.univ.filter fun j : Fin n ↦ x j = i)]
  · simp [tupleCount, multinomialCount]
  · intro j
    simp

/-- Helper for Theorem 5.35: if a color does not appear in a word, then its histogram entry is
zero. -/
private theorem tupleCount_eq_zero_of_not_mem_image (x : Fin n → Fin m) {i : Fin m}
    (hi : i ∉ Finset.univ.image x) :
    tupleCount x i = 0 := by
  -- Proof comment: rewrite the histogram entry as a list count and use that `i` is absent from
  -- the word exactly when it is absent from the image of `x`.
  rw [tupleCount_eq_listCount]
  apply List.count_eq_zero_of_not_mem
  simpa [List.mem_ofFn', Set.mem_range, Finset.mem_image] using hi

/-- Helper for Theorem 5.35: coordinate permutations preserve the histogram `tupleCount`. -/
private theorem tupleCount_eq_of_mem_coordinatePermutationOrbit
    (x x₀ : Fin n → Fin m)
    (hx : x ∈ MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) :
    tupleCount x = tupleCount x₀ := by
  obtain ⟨g, rfl⟩ := MulAction.mem_orbit_iff.mp hx
  ext i
  -- Proof comment: passing from `x₀` to `g • x₀` only reorders coordinates, so the associated
  -- word lists are permutations and therefore have identical letter counts.
  rw [tupleCount_eq_listCount, tupleCount_eq_listCount]
  simpa [DomMulAct.smul_apply] using
    (Equiv.Perm.ofFn_comp_perm (DomMulAct.mk.symm g) x₀).count_eq i

/-- Helper for Theorem 5.35: words with the same histogram differ by a permutation of their
coordinates. -/
private theorem mem_coordinatePermutationOrbit_of_tupleCount_eq
    (x x₀ : Fin n → Fin m) (hx : tupleCount x = tupleCount x₀) :
    x ∈ MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀ := by
  classical
  have hcard :
      ∀ i : Fin m, Fintype.card {j // x j = i} = Fintype.card {j // x₀ j = i} := by
    intro i
    -- Proof comment: equal histograms mean the color fibers of `x` and `x₀` have the same size.
    rw [fintypeCard_fiber_eq_tupleCount, fintypeCard_fiber_eq_tupleCount]
    exact congrArg (fun f => f i) hx
  let e : ∀ i : Fin m, {j // x j = i} ≃ {j // x₀ j = i} := fun i ↦
    Classical.choice (Fintype.card_eq.mp (hcard i))
  let σFun : Fin n → Fin n := fun j ↦ (e (x j) ⟨j, rfl⟩).1
  let σInv : Fin n → Fin n := fun j ↦ ((e (x₀ j)).symm ⟨j, rfl⟩).1
  have hσFun_eq :
      ∀ {j : Fin n} {i : Fin m} (h : x j = i), σFun j = (e i ⟨j, h⟩).1 := by
    intro j i h
    subst h
    rfl
  have hσInv_eq :
      ∀ {j : Fin n} {i : Fin m} (h : x₀ j = i), σInv j = ((e i).symm ⟨j, h⟩).1 := by
    intro j i h
    subst h
    rfl
  have hLeft : Function.LeftInverse σInv σFun := by
    intro j
    -- Proof comment: by construction, `σFun` sends the `x`-fiber of `j` to the corresponding
    -- `x₀`-fiber, and `σInv` applies the inverse equivalence on that same fiber.
    rw [hσInv_eq ((e (x j) ⟨j, rfl⟩).2)]
    exact congrArg Subtype.val ((e (x j)).left_inv ⟨j, rfl⟩)
  have hRight : Function.RightInverse σInv σFun := by
    intro j
    -- Proof comment: the same fiberwise inverse argument proves the opposite composition is the
    -- identity as well.
    rw [hσFun_eq (((e (x₀ j)).symm ⟨j, rfl⟩).2)]
    exact congrArg Subtype.val (((e (x₀ j)).symm).left_inv ⟨j, rfl⟩)
  let sigmaPerm : Equiv.Perm (Fin n) :=
    ⟨σFun, σInv, hLeft, hRight⟩
  refine MulAction.mem_orbit_iff.mpr ?_
  refine ⟨DomMulAct.mk sigmaPerm, ?_⟩
  ext j
  -- Proof comment: the assembled permutation sends each coordinate of `x` to a coordinate of
  -- `x₀` carrying the same color.
  simpa [sigmaPerm, σFun, DomMulAct.smul_apply] using congrArg Fin.val ((e (x j) ⟨j, rfl⟩).2)

/-- Helper for Theorem 5.35: the stabilizer of a word under coordinate permutations has
cardinality `∏ i, (tupleCount x i)!`. -/
private theorem coordinatePermutationStabilizerCard_eq_prodFactorial
    (x : Fin n → Fin m) :
    Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x) =
      ∏ i, Nat.factorial (tupleCount x i) := by
  classical
  have hcard :
      Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x) =
        ∏ i ∈ Finset.univ.image x, Nat.factorial (tupleCount x i) := by
    -- Proof comment: rewrite the stabilizer as the subtype of permutations preserving `x`, then
    -- apply the dedicated `DomMulAct.stabilizer_card'` theorem.
    rw [← Nat.card_eq_fintype_card,
      Nat.card_congr
        ((DomMulAct.mk.symm : ((Equiv.Perm (Fin n))ᵈᵐᵃ) ≃ Equiv.Perm (Fin n)).subtypeEquiv
          (p := fun g ↦ g ∈ MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x)
          (q := fun g : Equiv.Perm (Fin n) ↦ x ∘ g = x)
          (fun g ↦ DomMulAct.mem_stabilizer_iff (f := x) (g := g))),
      Nat.card_eq_fintype_card]
    simpa [Function.comp, fintypeCard_fiber_eq_tupleCount] using
      (DomMulAct.stabilizer_card' (f := x))
  calc
    Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x) =
        ∏ i ∈ Finset.univ.image x, Nat.factorial (tupleCount x i) := hcard
    _ = ∏ i, Nat.factorial (tupleCount x i) := by
      -- Proof comment: colors outside the image contribute `0! = 1`, so the product can be
      -- extended from the image of `x` to all colors.
      exact Finset.prod_subset (by simp) fun i _ hi ↦ by
        simp [tupleCount_eq_zero_of_not_mem_image x hi]

/-- Helper for Theorem 5.35: the orbit of a word with histogram `k` has cardinality equal to the
multinomial coefficient `Nat.multinomial Finset.univ k`. -/
private theorem card_coordinatePermutationOrbit_eq_multinomial
    (x₀ : Fin n → Fin m) (k : Fin m → ℕ) (hx₀ : tupleCount x₀ = k) :
    Nat.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) =
      Nat.multinomial Finset.univ k := by
  classical
  let orbitCard : ℕ := Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀)
  have hk_sum : ∑ i, k i = n := by
    -- Proof comment: the total of the histogram of any word is the word length `n`.
    calc
      ∑ i, k i = ∑ i, tupleCount x₀ i := by simp [hx₀]
      _ = n := by
        simpa [tupleCount] using
          sum_multinomialCount (X := fun j ↦ fun y : Fin n → Fin m ↦ y j) x₀
  have hgroup :
      Fintype.card ((Equiv.Perm (Fin n))ᵈᵐᵃ) = Nat.factorial n := by
    calc
      Fintype.card ((Equiv.Perm (Fin n))ᵈᵐᵃ) = Fintype.card (Equiv.Perm (Fin n)) := by
        simpa using
          (Fintype.card_congr
            (DomMulAct.mk : Equiv.Perm (Fin n) ≃ ((Equiv.Perm (Fin n))ᵈᵐᵃ))).symm
      _ = Nat.factorial n := by
        simpa using (Fintype.card_perm (α := Fin n))
  have horbit :
      orbitCard * ∏ i, Nat.factorial (tupleCount x₀ i) = Nat.factorial n := by
    -- Proof comment: orbit-stabilizer converts the orbit size into the group cardinal divided by
    -- the stabilizer size, and the acting group is the full permutation group on `Fin n`.
    calc
      orbitCard * ∏ i, Nat.factorial (tupleCount x₀ i)
          = Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) *
              ∏ i, Nat.factorial (tupleCount x₀ i) := by
            rfl
      _ = Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) *
              Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) := by
            rw [coordinatePermutationStabilizerCard_eq_prodFactorial]
      _ = Fintype.card ((Equiv.Perm (Fin n))ᵈᵐᵃ) := by
            exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
              (((Equiv.Perm (Fin n))ᵈᵐᵃ)) x₀
      _ = Nat.factorial n := hgroup
  have hmultinomial :
      Nat.multinomial Finset.univ k * ∏ i, Nat.factorial (tupleCount x₀ i) = Nat.factorial n := by
    -- Proof comment: this is exactly the standard multinomial identity after rewriting the
    -- histogram of `x₀` as `k`.
    rw [show (∏ i, Nat.factorial (tupleCount x₀ i)) = ∏ i, Nat.factorial (k i) by simp [hx₀]]
    rw [mul_comm]
    simpa [hk_sum] using (Nat.multinomial_spec (s := Finset.univ) (f := k))
  have hpos : 0 < ∏ i, Nat.factorial (tupleCount x₀ i) := by
    -- Proof comment: factorials are positive, so the common factor can be cancelled.
    exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos _
  have horbitCard : orbitCard = Nat.multinomial Finset.univ k :=
    Nat.mul_right_cancel hpos (horbit.trans hmultinomial.symm)
  simpa [orbitCard, Nat.card_eq_fintype_card] using horbitCard

/-- Helper for Theorem 5.35: an independent family with common law `p` has multinomial singleton
mass on its count vector. -/
theorem multinomialCount_preimage_singleton_eq_multinomial
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ)
    (hk : k ∈ Finset.piAntidiag Finset.univ n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := by
  classical
  let sampleVec : Ω → Fin n → Fin m := fun ω j ↦ X j ω
  haveI : IsProbabilityMeasure (μ.map sampleVec) := by
    refine ⟨?_⟩
    rw [Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_lambda _ fun i ↦ (h_law i).aemeasurable) MeasurableSet.univ]
    simp
  have hk_sum : ∑ i, k i = n := by
    simpa [Finset.mem_piAntidiag] using hk
  obtain ⟨x₀, hx₀⟩ := exists_word_with_tupleCount k hk_sum
  have h_preimage :
      multinomialCount X ⁻¹' {k} = sampleVec ⁻¹' {x | tupleCount x = k} := by
    -- Proof comment: evaluating `multinomialCount X` at `ω` is the same as evaluating the
    -- deterministic word-count map on the sampled word `sampleVec ω`.
    ext ω
    rfl
  have h_push :
      μ (multinomialCount X ⁻¹' {k}) = (μ.map sampleVec) {x | tupleCount x = k} := by
    -- Proof comment: after the event rewrite above, pass from the original probability space to
    -- the finite word space by the pushforward measure of `sampleVec`.
    rw [h_preimage, Measure.map_apply_of_aemeasurable
      (aemeasurable_pi_lambda _ fun i ↦ (h_law i).aemeasurable)]
    exact (Set.toFinite _).measurableSet
  have hx₀mass : (μ.map sampleVec).toPMF x₀ = ∏ i, (p i) ^ k i := by
    -- Proof comment: the chosen representative word has the prescribed histogram `k`, so its
    -- singleton mass is the common histogram weight.
    rw [Measure.toPMF_apply]
    rw [sampleVecPointMass_eq_prod p X h_indep h_law x₀]
    exact sampleWordWeight_eq_prodPow_of_tupleCount_eq p x₀ k hx₀
  have h_common_weight :
      ∀ x : Fin n → Fin m, tupleCount x = k →
        (μ.map sampleVec).toPMF x = ∏ i, (p i) ^ k i := by
    intro x hx
    rw [Measure.toPMF_apply]
    rw [sampleVecPointMass_eq_prod p X h_indep h_law x]
    exact sampleWordWeight_eq_prodPow_of_tupleCount_eq p x k hx
  let orbitFinset : Finset (Fin n → Fin m) :=
    (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀).toFinite.toFinset
  have h_countClass_eq_orbit :
      {x | tupleCount x = k} = MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀ := by
    ext x
    constructor
    · intro hx
      -- Proof comment: matching histograms force `x` and `x₀` to differ only by a coordinate
      -- permutation.
      exact mem_coordinatePermutationOrbit_of_tupleCount_eq x x₀ (hx.trans hx₀.symm)
    · intro hx
      -- Proof comment: conversely, coordinate permutations do not change the histogram.
      exact (tupleCount_eq_of_mem_coordinatePermutationOrbit x x₀ hx).trans hx₀
  have h_mass_sum :
      (μ.map sampleVec) {x | tupleCount x = k} =
        Finset.sum orbitFinset (fun x ↦ (μ.map sampleVec).toPMF x) := by
    -- Proof comment: once the histogram class is identified with the orbit, the finite-space mass
    -- is the sum of the point masses over that orbit.
    have horbitSet : (orbitFinset : Set (Fin n → Fin m)) =
        MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀ := by
      simp [orbitFinset]
    calc
      (μ.map sampleVec) {x | tupleCount x = k}
          = (μ.map sampleVec) (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) := by
              rw [h_countClass_eq_orbit]
      _ = (μ.map sampleVec) (orbitFinset : Set (Fin n → Fin m)) := by
            rw [← horbitSet]
      _ = Finset.sum orbitFinset (fun x ↦ (μ.map sampleVec).toPMF x) := by
            have hMeasureEval :
                (μ.map sampleVec).toPMF.toMeasure (orbitFinset : Set (Fin n → Fin m)) =
                  (μ.map sampleVec) (orbitFinset : Set (Fin n → Fin m)) := by
              exact congrArg
                (fun ν : Measure (Fin n → Fin m) ↦ ν (orbitFinset : Set (Fin n → Fin m)))
                (Measure.toPMF_toMeasure (μ := μ.map sampleVec))
            rw [← hMeasureEval]
            simpa using ((μ.map sampleVec).toPMF.toMeasure_apply_finset orbitFinset)
  calc
    μ (multinomialCount X ⁻¹' {k})
        = (μ.map sampleVec) {x | tupleCount x = k} := h_push
    _ = Finset.sum orbitFinset (fun x ↦ (μ.map sampleVec).toPMF x) := h_mass_sum
    _ = Finset.sum orbitFinset (fun _x ↦ ∏ i, (p i) ^ k i) := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      apply h_common_weight
      have hxOrbit : x ∈ MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀ := by
        simpa [orbitFinset] using hx
      exact (tupleCount_eq_of_mem_coordinatePermutationOrbit x x₀ hxOrbit).trans hx₀
    _ = ((orbitFinset.card : ℕ) : ENNReal) *
          ∏ i, (p i) ^ k i := by
      simp [nsmul_eq_mul]
    _ = (Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) : ENNReal) *
          ∏ i, (p i) ^ k i := by
      have hcard :
          orbitFinset.card = Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) := by
        unfold orbitFinset
        exact Set.Finite.card_toFinset (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀).toFinite
      exact congrArg (fun t : ℕ => (t : ENNReal) * ∏ i, (p i) ^ k i) hcard
    _ = (Nat.multinomial Finset.univ k : ENNReal) * ∏ i, (p i) ^ k i := by
      congr 1
      simpa [Nat.card_eq_fintype_card] using
        congrArg (fun t : ℕ => (t : ENNReal))
          (card_coordinatePermutationOrbit_eq_multinomial x₀ k hx₀)

/-- Helper for Theorem 5.35: the multinomial singleton-mass formula can be written using the
sum condition `∑ i, k i = n` instead of membership in `Finset.piAntidiag`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := by
  simpa [Finset.mem_piAntidiag, hk] using
    multinomialCount_preimage_singleton_eq_multinomial p X h_indep h_law k

end

end Theorem535Local

open Theorem535Local

noncomputable section

/-- The counting process obtained from a Poisson number of marks on `[0,1]`, where `L` is the
random number of marks and `X n` is the location of the `n`th mark as an `I`-valued random
variable. The count at time `t` records how many of the first `L` marks fall in `(0,t]`. -/
def poissonizedUniformCountingProcess (L : Ω → ℕ) (X : ℕ → Ω → I) :
    I → Ω → ℕ :=
  fun t ω ↦ Finset.sum (Finset.Icc 1 (L ω))
    (fun i ↦ if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0)

section

omit [MeasurableSpace Ω]

/-- The Poissonized counting process counts the marks among `X 1, …, X (L ω)` that lie in
`(0,t]`. -/
theorem poissonizedUniformCountingProcess_apply (L : Ω → ℕ) (X : ℕ → Ω → I)
    (t : I) (ω : Ω) :
    poissonizedUniformCountingProcess L X t ω =
      Finset.sum (Finset.Icc 1 (L ω))
        (fun i ↦ if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) :=
  rfl

end

-- Proof sketch: for a finite increasing grid `0 = t₀ < ⋯ < t_m ≤ 1`, identify the increment
-- `N_{t_i} - N_{t_{i-1}}` with the number of indices `l ≤ L` whose mark lies in `(t_{i-1}, t_i]`.
-- Conditional on `L = n`, these counts are multinomial with cell probabilities
-- `t_i - t_{i-1}` because the marks are i.i.d. uniform on `[0,1]`; multiplying by the Poisson law
-- of `L` shows that the increments are independent Poisson with parameters
-- `α (t_i - t_{i-1})`.
section

variable (P : Measure Ω) [IsProbabilityMeasure P] (α : NNReal) (L : Ω → ℕ) (X : ℕ → Ω → I)

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: subtracting the indicators of `(0,t]` and `(0,s]` isolates the
intermediate cell `(s,t]`. -/
theorem poissonized_uniform_indicator_sub_eq_interval_indicator {x s t : I} (hst : s ≤ t) :
    (if (0 : I) < x ∧ x ≤ t then 1 else 0) - (if (0 : I) < x ∧ x ≤ s then 1 else 0) =
      (if s < x ∧ x ≤ t then 1 else 0) := by
  -- Split on whether the point lies in `(0,t]`; this reduces the claim to the two geometric cases.
  by_cases hit : (0 : I) < x ∧ x ≤ t
  · rcases hit with ⟨h0, hxt⟩
    by_cases hs : x ≤ s
    · have hs' : (0 : I) < x ∧ x ≤ s := ⟨h0, hs⟩
      have hnot : ¬(s < x ∧ x ≤ t) := by
        intro hsx
        exact not_lt_of_ge hs hsx.1
      simp [hxt, hs']
    · have hsx : s < x := lt_of_not_ge hs
      have hs' : ¬((0 : I) < x ∧ x ≤ s) := by
        intro h
        exact hs h.2
      have hx0 : x ≠ 0 := ne_of_gt h0
      simp [hxt, hs', hsx, hx0]
  · have hs' : ¬((0 : I) < x ∧ x ≤ s) := by
      intro hs
      exact hit ⟨hs.1, hs.2.trans hst⟩
    have hnot : ¬(s < x ∧ x ≤ t) := by
      intro hsx
      exact hit ⟨lt_of_le_of_lt (show (0 : I) ≤ s from bot_le) hsx.1, hsx.2⟩
    simp [hit, hs', hnot]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: each increment of the Poissonized counting process is the number of
marks among `X 1, …, X (L ω)` that fall in the half-open interval `(s,t]`. -/
theorem poissonizedUniformCountingProcess_increment_eq_interval_count {s t : I} (hst : s ≤ t)
    (ω : Ω) :
    poissonizedUniformCountingProcess L X t ω - poissonizedUniformCountingProcess L X s ω =
      Finset.sum (Finset.Icc 1 (L ω))
        (fun i ↦ if s < X i ω ∧ X i ω ≤ t then 1 else 0) := by
  rw [poissonizedUniformCountingProcess, poissonizedUniformCountingProcess]
  -- Rewrite the increment as a sum of termwise differences.
  calc
    (∑ i ∈ Finset.Icc 1 (L ω), if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) -
        (∑ i ∈ Finset.Icc 1 (L ω), if (0 : I) < X i ω ∧ X i ω ≤ s then 1 else 0) =
      ∑ i ∈ Finset.Icc 1 (L ω),
        ((if (0 : I) < X i ω ∧ X i ω ≤ t then 1 else 0) -
          (if (0 : I) < X i ω ∧ X i ω ≤ s then 1 else 0)) := by
        symm
        refine Finset.sum_tsub_distrib (Finset.Icc 1 (L ω)) ?_
        intro i hi
        by_cases hit : (0 : I) < X i ω ∧ X i ω ≤ t
        · rcases hit with ⟨h0, hxt⟩
          by_cases hs : X i ω ≤ s
          · simp [hxt, h0, hs]
          · simp [hxt, h0, hs]
        · have hs' : ¬((0 : I) < X i ω ∧ X i ω ≤ s) := by
            intro hs
            exact hit ⟨hs.1, hs.2.trans hst⟩
          simp [hit, hs']
    -- Collapse each summand to the indicator of the cell `(s,t]`.
    _ = ∑ i ∈ Finset.Icc 1 (L ω), if s < X i ω ∧ X i ω ≤ t then 1 else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      exact poissonized_uniform_indicator_sub_eq_interval_indicator hst

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the Poissonized counting process starts at zero because `(0,0]` is
empty. -/
theorem poissonizedUniformCountingProcess_zero_eq :
    poissonizedUniformCountingProcess L X 0 = 0 := by
  ext ω
  rw [poissonizedUniformCountingProcess]
  -- Every summand vanishes because no point can satisfy `x ≤ 0` and `0 < x` simultaneously.
  refine Finset.sum_eq_zero ?_
  intro i hi
  by_cases h0 : (0 : I) < X i ω
  · have hx0 : X i ω ≠ 0 := ne_of_gt h0
    simp [h0, hx0]
  · simp [h0]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the Poissonized counting process is nondecreasing in time, since
increasing the right endpoint can only add marked points to the half-open interval `(0,t]`. -/
theorem poissonizedUniformCountingProcess_mono :
    Monotone (poissonizedUniformCountingProcess L X) := by
  intro s t hst ω
  rw [poissonizedUniformCountingProcess, poissonizedUniformCountingProcess]
  refine Finset.sum_le_sum ?_
  intro i hi
  by_cases hs : (0 : I) < X i ω ∧ X i ω ≤ s
  · have ht : (0 : I) < X i ω ∧ X i ω ≤ t := ⟨hs.1, hs.2.trans hst⟩
    simp [hs, ht]
  · by_cases ht : (0 : I) < X i ω ∧ X i ω ≤ t
    · by_cases hxs : X i ω ≤ s
      · have hs' : (0 : I) < X i ω ∧ X i ω ≤ s := ⟨ht.1, hxs⟩
        exact (hs hs').elim
      · simp [ht, hxs]
    · simp [hs, ht]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: counting the grid points strictly below `x` always produces a valid
index in the full grid because the terminal grid point is `1`. -/
theorem fullGridLabel_card_lt {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (x : I) :
    (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card < m + 1 := by
  -- Proof comment: the last grid point is `1`, so it can never lie strictly below a point of `I`.
  have hlast_not_mem :
      Fin.last m ∉ Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x := by
    have hx_le_one : x ≤ (1 : I) := x.2.2
    have hnot_lt : ¬u (Fin.last m) < x := by
      rw [h1]
      exact not_lt_of_ge hx_le_one
    simp [hnot_lt]
  simpa using Finset.card_lt_univ_of_notMem hlast_not_mem

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the full-grid label of a point is the number of grid points lying
strictly below it. This turns the half-open grid cells into exact successor fibers. -/
noncomputable def fullGridLabel {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) : I → Fin (m + 1) :=
  fun x ↦
    ⟨(Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card,
      fullGridLabel_card_lt u h1 x⟩

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: any point in the half-open cell `(u i, u (i+1)]` receives the
successor label `i + 1`. -/
theorem fullGridLabel_eq_succ_of_mem_Ioc {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) {x : I}
    (hx : u i.castSucc < x ∧ x ≤ u i.succ) :
    fullGridLabel u h1 x = i.succ := by
  -- Proof comment: monotonicity shows that the indices below `x` are exactly `0, …, i`.
  have hfilter :
      Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) = Finset.Iic i.castSucc := by
    apply Finset.ext
    intro j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iic]
    constructor
    · intro hj
      by_contra hji
      have hij : i.succ ≤ j := by
        exact Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hji)
      have hux : x ≤ u j := le_trans hx.2 (hu hij)
      exact (not_lt_of_ge hux) hj
    · intro hj
      exact lt_of_le_of_lt (hu hj) hx.1
  apply Fin.ext
  simp [fullGridLabel, hfilter]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: if the full-grid label is `i + 1`, then the point lies in the
corresponding half-open cell `(u i, u (i+1)]`. -/
theorem fullGridLabel_mem_Ioc_of_eq_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) {x : I}
    (hx : fullGridLabel u h1 x = i.succ) :
    x ∈ Set.Ioc (u i.castSucc) (u i.succ) := by
  have hcard_eq :
      (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card = i.succ := by
    simpa [fullGridLabel] using congrArg Fin.val hx
  constructor
  · -- Proof comment: if `x` were at or below `u i`, then fewer than `i + 1` grid points could lie
    -- strictly below `x`, contradicting the label value.
    by_contra hx_le
    have hsubset :
        Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) ⊆ Finset.Iio i.castSucc := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
      simp only [Finset.mem_Iio]
      by_contra hj'
      have hij : i.castSucc ≤ j := le_of_not_gt hj'
      have hxuj : x ≤ u j := le_trans (not_lt.mp hx_le) (hu hij)
      exact (not_lt_of_ge hxuj) hj
    have hcard_le :
        (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card ≤ (Finset.Iio i.castSucc).card :=
      Finset.card_le_card hsubset
    simp [hcard_eq] at hcard_le
  · -- Proof comment: if `x` were strictly above `u (i + 1)`, then the first `i + 2` grid points
    -- would all lie below `x`, again contradicting the label value.
    by_contra hx_gt
    have hsubset :
        Finset.Iic i.succ ⊆ Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x) := by
      intro j hj
      have hj_le : j ≤ i.succ := by
        simpa only [Finset.mem_Iic] using hj
      have hjx : u j < x := lt_of_le_of_lt (hu hj_le) (lt_of_not_ge hx_gt)
      simp [hjx]
    have hcard_le :
        (Finset.Iic i.succ).card ≤
          (Finset.univ.filter (fun j : Fin (m + 1) ↦ u j < x)).card :=
      Finset.card_le_card hsubset
    simp [hcard_eq] at hcard_le

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the successor fiber of `fullGridLabel` is exactly the corresponding
half-open grid cell. -/
theorem fullGridLabel_preimage_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) :
    fullGridLabel u h1 ⁻¹' ({i.succ} : Set (Fin (m + 1))) = Set.Ioc (u i.castSucc) (u i.succ) := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    exact fullGridLabel_mem_Ioc_of_eq_succ u hu h1 i hx
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact fullGridLabel_eq_succ_of_mem_Ioc u hu h1 i hx

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the zero fiber of the full-grid label is exactly the singleton
`{0}`. -/
theorem fullGridLabel_preimage_zero {m : ℕ} (u : Fin (m + 1) → I)
    (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    fullGridLabel u h1 ⁻¹' ({0} : Set (Fin (m + 1))) = ({0} : Set I) := by
  ext x
  constructor
  · intro hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    by_contra hx0
    have hx_pos : (0 : I) < x := lt_of_le_of_ne x.2.1 (Ne.symm hx0)
    have hzero_mem :
        (0 : Fin (m + 1)) ∈ Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x := by
      have hu0x : u 0 < x := by
        simpa [h0] using hx_pos
      simp [hu0x]
    have hcard_pos :
        0 < (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card :=
      Finset.card_pos.mpr ⟨0, hzero_mem⟩
    have hcard_zero :
        (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card = 0 := by
      simpa [fullGridLabel] using congrArg Fin.val hx
    have hnot_pos :
        ¬0 <
          (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < x).card := by
      simp [hcard_zero]
    exact hnot_pos hcard_pos
  · intro hx
    simp only [Set.mem_singleton_iff] at hx
    subst hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    apply Fin.ext
    have hfilter_empty :
        Finset.univ.filter (fun i : Fin (m + 1) ↦ u i < (0 : I)) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      exact (not_lt_of_ge (u i).2.1) hi
    have hcard_zero :
        (Finset.univ.filter fun i : Fin (m + 1) ↦ u i < (0 : I)).card = 0 := by
      rw [hfilter_empty]
      simp
    simp [fullGridLabel]

/-- Helper for Theorem 5.35: a full-grid label map is measurable once the singleton fibers have
been identified by the zero and successor cell descriptions. -/
theorem measurable_fullGridLabel {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    Measurable (fullGridLabel u h1) := by
  -- Proof comment: the codomain is finite, so it is enough to show that every singleton fiber is
  -- measurable, and those fibers are exactly `{0}` or one of the half-open grid cells.
  refine measurable_to_countable' ?_
  intro i
  rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨j, rfl⟩
  · rw [fullGridLabel_preimage_zero u h0 h1]
    exact measurableSet_singleton 0
  · rw [fullGridLabel_preimage_succ u hu h1 j]
    exact measurableSet_Ioc

/-- Helper for Theorem 5.35: the common law of a full-grid label under the uniform measure on `I`
is the pushforward PMF of `volume` along the full-grid label map. -/
noncomputable def fullGridLabelPMF {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) : PMF (Fin (m + 1)) :=
  letI : IsProbabilityMeasure ((volume : Measure I).map (fullGridLabel u h1)) :=
    Measure.isProbabilityMeasure_map
      (measurable_fullGridLabel u hu h0 h1).aemeasurable
  (Measure.map (fullGridLabel u h1) (volume : Measure I)).toPMF

/-- Helper for Theorem 5.35: `fullGridCount u h1 L X ω i` counts how many of the first `L ω`
marks receive the full-grid label `i`, written directly with the Chapter 2 count vector
`multinomialCount`. -/
def fullGridCount {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (L : Ω → ℕ) (X : ℕ → Ω → I) (ω : Ω) :
    Fin (m + 1) → ℕ :=
  multinomialCount (fun j : Fin (L ω) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω

section

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: composing the uniform marks with the measurable full-grid label map
gives the pushforward law of the label partition. -/
theorem fullGridLabel_hasLaw {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P) :
    HasLaw
      (fun ω ↦ fullGridLabel u h1 (X (n + 1) ω))
      (fullGridLabelPMF u hu h0 h1).toMeasure P := by
  have h_label :
      HasLaw (fullGridLabel u h1) ((volume : Measure I).map (fullGridLabel u h1))
        (volume : Measure I) := by
    exact
      (show MeasurePreserving (fullGridLabel u h1) (volume : Measure I)
          ((volume : Measure I).map (fullGridLabel u h1)) from
        ⟨measurable_fullGridLabel u hu h0 h1, rfl⟩).hasLaw
  -- Proof comment: transport the uniform law of `X (n + 1)` through the full-grid label map.
  simpa [fullGridLabelPMF, Measure.toPMF_toMeasure] using h_label.fun_comp (hX_law n)

/-- Helper for Theorem 5.35: the zero-mass of the full-grid label distribution vanishes because
the zero fiber is the singleton `{0}`, which has zero volume in `I`. -/
theorem fullGridLabel_toPMF_apply_zero {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    fullGridLabelPMF u hu h0 h1 0 = 0 := by
  -- Proof comment: rewrite the singleton mass by the zero-fiber identity and collapse the
  -- resulting singleton volume.
  rw [fullGridLabelPMF]
  rw [Measure.toPMF_apply]
  rw [Measure.map_apply
    (measurable_fullGridLabel u hu h0 h1) (measurableSet_singleton 0)]
  rw [fullGridLabel_preimage_zero u h0 h1]
  simp

/-- Helper for Theorem 5.35: every successor mass of the full-grid label distribution is exactly
the volume of the corresponding half-open cell. -/
theorem fullGridLabel_toPMF_apply_succ {m : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) (i : Fin m) :
    fullGridLabelPMF u hu h0 h1 i.succ =
      volume (Set.Ioc (u i.castSucc) (u i.succ)) := by
  -- Proof comment: the successor fiber was already identified as the corresponding half-open
  -- grid cell, so its label mass is that cell's volume.
  rw [fullGridLabelPMF]
  rw [Measure.toPMF_apply]
  rw [Measure.map_apply
    (measurable_fullGridLabel u hu h0 h1) (measurableSet_singleton i.succ)]
  rw [fullGridLabel_preimage_succ u hu h1 i]

/-- Helper for Theorem 5.35: restricting a sequence of marks to a finite prefix and then applying
the full-grid label coordinatewise is measurable. -/
theorem measurable_prefix_fullGridLabel_tuple {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) :
    Measurable (fun x : ℕ → I ↦ fun j : Fin n ↦ fullGridLabel u h1 (x j)) := by
  -- Proof comment: each coordinate is an evaluation map followed by the measurable label map.
  refine measurable_pi_lambda _ ?_
  intro j
  exact (measurable_fullGridLabel u hu h0 h1).comp (measurable_pi_apply (j : ℕ))

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the labeled first `n` marks remain independent after composing the
uniform marks with the measurable full-grid label map and restricting to the prefix `Fin n`. -/
theorem iIndepFun_prefix_fullGridLabel {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hX_indep : iIndepFun (fun n ↦ X (n + 1)) P) :
    iIndepFun
      (fun j : Fin n ↦ fun ω ↦ fullGridLabel u h1 (X (j + 1) ω)) P := by
  have hlabel_indep :
      iIndepFun (fun k : ℕ ↦ fun ω ↦ fullGridLabel u h1 (X (k + 1) ω)) P := by
    -- Proof comment: postcompose each independent coordinate with the measurable label map.
    exact hX_indep.comp (fun _ ↦ fullGridLabel u h1)
      (fun _ ↦ measurable_fullGridLabel u hu h0 h1)
  -- Proof comment: the finite prefix is obtained by precomposing with `Fin.val`.
  simpa using hlabel_indep.precomp Fin.val_injective

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the Poisson length variable is independent of the label-count vector
of any fixed finite prefix of labeled marks. -/
theorem indep_length_multinomialCount_fullGridLabel {m n : ℕ} (u : Fin (m + 1) → I)
    (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P) :
    IndepFun L
      (fun ω ↦
        multinomialCount
          (fun j : Fin n ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω) P := by
  let prefixTuple : (ℕ → I) → (Fin n → Fin (m + 1)) :=
    fun x j ↦ fullGridLabel u h1 (x j)
  let countMap : (Fin n → Fin (m + 1)) → (Fin (m + 1) → ℕ) :=
    fun y ↦ multinomialCount (fun j : Fin n ↦ fun y' : Fin n → Fin (m + 1) ↦ y' j) y
  have hprefix_meas : Measurable prefixTuple :=
    measurable_prefix_fullGridLabel_tuple u hu h0 h1
  have hcount_meas : Measurable countMap :=
    measurable_of_finite _
  -- Proof comment: compose the sequence-valued independent partner first with the finite prefix
  -- label tuple, then with the deterministic count map on that finite tuple.
  simpa [prefixTuple, countMap, Function.comp] using
    hLX_indep.comp measurable_id (hcount_meas.comp hprefix_meas)

end

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the entries of the random-length full-grid count vector sum to the
realized sample size `L ω`. -/
theorem sum_fullGridCount {m : ℕ} (u : Fin (m + 1) → I)
    (h1 : u (Fin.last m) = 1) (ω : Ω) :
    ∑ i, fullGridCount u h1 L X ω i = L ω := by
  -- Proof comment: `fullGridCount` is defined by applying `multinomialCount` to the finite prefix
  -- of length `L ω`, so the total count is exactly that prefix length.
  simpa [fullGridCount] using
    sum_multinomialCount
      (fun j : Fin (L ω) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: on the event `L ω = n`, the random-length full-grid count vector is
exactly the fixed-length label-count vector of the first `n` marks. -/
theorem fullGridCount_eq_multinomialCount_of_length_eq {m n : ℕ}
    (u : Fin (m + 1) → I) (h1 : u (Fin.last m) = 1) {ω : Ω}
    (hLn : L ω = n) :
    fullGridCount u h1 L X ω =
      multinomialCount
        (fun j : Fin n ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω := by
  -- Proof comment: after replacing `L ω` by `n`, both sides are definitionally the same count.
  subst hLn
  simp [fullGridCount]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the singleton event for the random-length full-grid count vector is
the intersection of the length event `L = ∑ i, k i` with the corresponding fixed-length sample
count event. -/
theorem fullGridCount_preimage_singleton_eq_length_inter_multinomialCount {m : ℕ}
    (u : Fin (m + 1) → I) (h1 : u (Fin.last m) = 1) (k : Fin (m + 1) → ℕ) :
    fullGridCount u h1 L X ⁻¹' {k} =
      {ω | L ω = ∑ i, k i} ∩
        {ω |
          multinomialCount
            (fun j : Fin (∑ i, k i) ↦ fun ω' ↦ fullGridLabel u h1 (X (j + 1) ω')) ω = k} := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    constructor
    · -- Proof comment: summing the coordinates of the count vector forces the sample length.
      have hsum : ∑ i, fullGridCount u h1 L X ω i = ∑ i, k i := by
        exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
      simpa [sum_fullGridCount L X u h1 ω] using hsum
    · -- Proof comment: once the length is fixed, the random-length count reduces to the fixed
      -- finite-sample count on the first `∑ i, k i` marks.
      have hLω : L ω = ∑ i, k i := by
        have hsum : ∑ i, fullGridCount u h1 L X ω i = ∑ i, k i := by
          exact congrArg (fun v : Fin (m + 1) → ℕ ↦ ∑ i, v i) hω
        simpa [sum_fullGridCount L X u h1 ω] using hsum
      simp only [Set.mem_setOf_eq]
      rw [← fullGridCount_eq_multinomialCount_of_length_eq L X u h1 hLω]
      exact hω
  · rintro ⟨hLω, hω⟩
    -- Proof comment: the fixed-length count identity rewrites the target event back to the
    -- random-length full-grid count event.
    simp only [Set.mem_setOf_eq] at hLω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    rw [fullGridCount_eq_multinomialCount_of_length_eq L X u h1 hLω]
    exact hω

omit [IsProbabilityMeasure P] in
private theorem iid_uniform_marks_hasLaw
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P) :
    ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P := by
  intro n
  simpa using (hX_iid.identDistrib 0 n).hasLaw hX1_law

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the full-grid count singleton event has the textbook
multinomial-times-Poisson mass obtained by conditioning on `L = ∑ i, k i`. -/
theorem fullGridCount_preimage_singleton_eq_multinomial_mul_poisson {m : ℕ}
    (u : Fin (m + 1) → I) (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hL : HasLaw L (poissonMeasure α) P)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P)
    (k : Fin (m + 1) → ℕ) :
    P (fullGridCount u h1 L X ⁻¹' {k}) =
      (poissonMeasure α) {∑ i, k i} *
        ((Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i) := by
  haveI : IsProbabilityMeasure P := hL.isProbabilityMeasure
  have hX_indep : iIndepFun (fun n ↦ X (n + 1)) P := hX_iid.iIndepFun
  have hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P :=
    iid_uniform_marks_hasLaw P X hX_iid hX1_law
  let Y : Fin (∑ i, k i) → Ω → Fin (m + 1) :=
    fun j ↦ fun ω ↦ fullGridLabel u h1 (X (j + 1) ω)
  have h_indep_count :
      IndepFun L (fun ω ↦ multinomialCount Y ω) P := by
    -- Proof comment: the length variable is independent of the fixed-prefix label-count vector.
    simpa [Y] using
      indep_length_multinomialCount_fullGridLabel P L X u hu h0 h1 hLX_indep
  have h_length_mass :
      P (L ⁻¹' ({∑ i, k i} : Set ℕ)) = (poissonMeasure α) {∑ i, k i} := by
    -- Proof comment: read the length singleton directly from the Poisson law of `L`.
    rw [← Measure.map_apply_of_aemeasurable hL.aemeasurable (measurableSet_singleton _), hL.map_eq]
  have h_count_mass :
      P ((fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) =
        (Nat.multinomial Finset.univ k : ENNReal) *
          ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i := by
    have hY_law : ∀ j, HasLaw (Y j) (fullGridLabelPMF u hu h0 h1).toMeasure P := by
      intro j
      simpa [Y] using fullGridLabel_hasLaw P X u hu h0 h1 hX_law
    -- Proof comment: conditional on the fixed length, the labeled marks have multinomial law.
    simpa [Y] using
      multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
        (fullGridLabelPMF u hu h0 h1) Y
        (iIndepFun_prefix_fullGridLabel P X u hu h0 h1 hX_indep)
        hY_law k rfl
  -- Proof comment: the event identity isolates the conditioning on `L = ∑ i, k i`.
  rw [fullGridCount_preimage_singleton_eq_length_inter_multinomialCount L X u h1 k]
  calc
    P ({ω | L ω = ∑ i, k i} ∩ {ω | multinomialCount Y ω = k}) =
        P (L ⁻¹' ({∑ i, k i} : Set ℕ) ∩
          (fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) := by
          rfl
    _ = P (L ⁻¹' ({∑ i, k i} : Set ℕ)) *
          P ((fun ω ↦ multinomialCount Y ω) ⁻¹' ({k} : Set (Fin (m + 1) → ℕ))) := by
          exact h_indep_count.measure_inter_preimage_eq_mul
            ({∑ i, k i} : Set ℕ) ({k} : Set (Fin (m + 1) → ℕ))
            (measurableSet_singleton _) (measurableSet_singleton _)
    _ = (poissonMeasure α) {∑ i, k i} *
          ((Nat.multinomial Finset.univ k : ENNReal) *
            ∏ i, (fullGridLabelPMF u hu h0 h1 i) ^ k i) := by
          rw [h_length_mass, h_count_mass]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the singleton mass of `poissonMeasure r` is the explicit Poisson
weight `poissonPMFReal r n`. -/
private lemma poissonMeasure_apply_singleton (r : NNReal) (n : ℕ) :
    poissonMeasure r ({n} : Set ℕ) = ENNReal.ofReal (poissonPMFReal r n) := by
  -- Proof comment: rewrite the Poisson measure as the measure associated to its PMF.
  simpa [poissonMeasure, poissonPMFReal_ofReal_eq_poissonPMF] using
    (PMF.toMeasure_apply_singleton (poissonPMF r) n (measurableSet_singleton n))

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the real-valued Poisson/multinomial mass factors into the product of
the corresponding Poisson singleton masses on each cell. -/
private lemma poissonMultinomialRealMass_eq_prodPoissonRealMass {m : ℕ}
    (q : Fin (m + 1) → NNReal) (hq : (∑ i, q i) = 1) (k : Fin (m + 1) → ℕ) :
    poissonPMFReal α (∑ i, k i) * Nat.multinomial Finset.univ k * ∏ i, ((q i : ℝ) ^ k i) =
      ∏ i, poissonPMFReal (α * q i) (k i) := by
  -- Proof comment: unfold the multinomial coefficient and then separate the exponential, power,
  -- and factorial contributions across the finite product.
  rw [Nat.multinomial]
  simp_rw [poissonPMFReal, div_eq_mul_inv]
  have hq' : (∑ i, (q i : ℝ)) = 1 := by
    simpa using congrArg (fun x : NNReal => (x : ℝ)) hq
  have hprod_ne : (↑(∏ i, (k i).factorial) : ℝ) ≠ 0 := by
    positivity
  have hfact_ne : (↑((∑ i, k i).factorial) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (∑ i, k i)
  have hdiv :
      (↑((∑ i, k i).factorial / ∏ i, (k i).factorial) : ℝ) =
        (↑((∑ i, k i).factorial) : ℝ) / ↑(∏ i, (k i).factorial) := by
    rw [Nat.cast_div (Nat.prod_factorial_dvd_factorial_sum Finset.univ k) hprod_ne]
  rw [hdiv]
  simp_rw [div_eq_mul_inv, mul_assoc]
  have hexp :
      ∏ x, Real.exp (-↑(α * q x)) = Real.exp (-↑α) := by
    rw [← Real.exp_sum]
    have hsum : (∑ x, -↑(α * q x)) = -(↑α * ∑ x, (q x : ℝ)) := by
      simp_rw [NNReal.coe_mul, Finset.sum_neg_distrib, ← Finset.mul_sum]
    rw [hsum, hq']
    simp
  have hpow :
      ∏ x, (↑(α * q x) : ℝ) ^ k x = ((↑α : ℝ) ^ (∑ x, k x)) * ∏ x, (q x : ℝ) ^ k x := by
    simp_rw [NNReal.coe_mul, mul_pow]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hinv :
      ∏ x, (↑(k x).factorial : ℝ)⁻¹ = (↑(∏ x, (k x).factorial) : ℝ)⁻¹ := by
    convert
      (Finset.prod_inv_distrib (s := Finset.univ) (f := fun x ↦ ((↑(k x).factorial : ℝ)))) using 1
    simp
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, hexp, hpow, hinv]
  field_simp [hprod_ne, hfact_ne]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the multinomial-times-Poisson singleton mass is exactly the singleton
mass of the product Poisson law on the grid cells. -/
theorem poissonMultinomialMass_eq_prodPoissonMass {m : ℕ}
    (p : PMF (Fin (m + 1))) (k : Fin (m + 1) → ℕ) :
    (poissonMeasure α) {∑ i, k i} * ((Nat.multinomial Finset.univ k : ENNReal) * ∏ i, p i ^ k i) =
      ∏ i, (poissonMeasure (α * (p i).toNNReal)) {k i} := by
  let q : Fin (m + 1) → NNReal := fun i ↦ (p i).toNNReal
  have hpcoe : ∀ i, p i = (q i : ENNReal) := by
    intro i
    exact (ENNReal.coe_toNNReal (p.apply_ne_top i)).symm
  have hqsum : (∑ i, q i) = 1 := by
    apply ENNReal.coe_inj.mp
    simpa [hpcoe, tsum_fintype] using p.tsum_coe
  have hpow :
      ∏ i, p i ^ k i = ENNReal.ofReal (∏ i, ((q i : ℝ) ^ k i)) := by
    -- Proof comment: each PMF weight is finite, so we can rewrite it through `toNNReal`.
    calc
      ∏ i, p i ^ k i = ∏ i, ((q i : ENNReal) ^ k i) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        rw [hpcoe]
      _ = ∏ i, ENNReal.ofReal ((q i : ℝ) ^ k i) := by
        refine Finset.prod_congr rfl ?_
        intro i hi
        simp
      _ = ENNReal.ofReal (∏ i, ((q i : ℝ) ^ k i)) := by
        symm
        exact ENNReal.ofReal_prod_of_nonneg (s := Finset.univ) (fun i hi ↦ by positivity)
  have hleft :
      (poissonMeasure α) {∑ i, k i} * ((Nat.multinomial Finset.univ k : ENNReal) * ∏ i, p i ^ k i) =
        ENNReal.ofReal
          (poissonPMFReal α (∑ i, k i) * Nat.multinomial Finset.univ k *
            ∏ i, ((q i : ℝ) ^ k i)) := by
    -- Proof comment: rewrite the Poisson singleton mass and the PMF weights into a single
    -- nonnegative real product.
    rw [poissonMeasure_apply_singleton, hpow, ← ENNReal.ofReal_natCast]
    calc
      ENNReal.ofReal (poissonPMFReal α (∑ i, k i)) *
          (ENNReal.ofReal ↑(Nat.multinomial Finset.univ k) *
            ENNReal.ofReal (∏ i, (q i : ℝ) ^ k i)) =
        ENNReal.ofReal (poissonPMFReal α (∑ i, k i)) *
          ENNReal.ofReal (↑(Nat.multinomial Finset.univ k) * ∏ i, (q i : ℝ) ^ k i) := by
            rw [← ENNReal.ofReal_mul]
            positivity
      _ =
        ENNReal.ofReal
          (poissonPMFReal α (∑ i, k i) *
            (↑(Nat.multinomial Finset.univ k) * ∏ i, (q i : ℝ) ^ k i)) := by
            have hmult_nonneg :
                0 ≤ (↑(Nat.multinomial Finset.univ k) : ℝ) * ∏ i, (q i : ℝ) ^ k i := by
              positivity
            exact (ENNReal.ofReal_mul poissonPMFReal_nonneg).symm
      _ =
        ENNReal.ofReal
          (poissonPMFReal α (∑ i, k i) * ↑(Nat.multinomial Finset.univ k) *
            ∏ i, (q i : ℝ) ^ k i) := by
            ring_nf
  have hright :
      ∏ i, (poissonMeasure (α * (p i).toNNReal)) {k i} =
        ENNReal.ofReal (∏ i, poissonPMFReal (α * q i) (k i)) := by
    -- Proof comment: the product Poisson singleton mass is the product of the coordinate
    -- Poisson weights, hence one `ofReal` of the finite real product.
    rw [show (∏ i, (poissonMeasure (α * (p i).toNNReal)) {k i}) =
        ∏ i, ENNReal.ofReal (poissonPMFReal (α * q i) (k i)) by
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [poissonMeasure_apply_singleton]]
    symm
    refine ENNReal.ofReal_prod_of_nonneg ?_
    intro i hi
    exact poissonPMFReal_nonneg
  rw [hleft, hright, poissonMultinomialRealMass_eq_prodPoissonRealMass (α := α) q hqsum k]

omit [IsProbabilityMeasure P] in
/-- Helper for Theorem 5.35: the whole full-grid count vector has the product Poisson law with
cell parameters `α * fullGridLabelPMF`. -/
theorem fullGridCountHasLawPiPoisson {m : ℕ}
    (u : Fin (m + 1) → I) (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1)
    (hL : HasLaw L (poissonMeasure α) P)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P) :
    HasLaw
      (fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i)
      (Measure.pi (fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))) P := by
  haveI : IsProbabilityMeasure P := hL.isProbabilityMeasure
  have hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P :=
    iid_uniform_marks_hasLaw P X hX_iid hX1_law
  let f : Ω → Fin (m + 1) → ℕ := fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i
  have hnull : NullMeasurable f P := by
    refine measurable_to_countable' ?_
    intro k
    change NullMeasurableSet (f ⁻¹' {k}) P
    rw [show f ⁻¹' {k} = fullGridCount u h1 L X ⁻¹' {k} by rfl]
    rw [fullGridCount_preimage_singleton_eq_length_inter_multinomialCount L X u h1 k]
    refine NullMeasurableSet.inter ?_ ?_
    · simpa [Set.preimage] using
        hL.aemeasurable.nullMeasurableSet_preimage (measurableSet_singleton (∑ i, k i))
    · let prefixTuple : Ω → Fin (∑ i, k i) → Fin (m + 1) :=
        fun ω j ↦ fullGridLabel u h1 (X (j + 1) ω)
      let countMap : (Fin (∑ i, k i) → Fin (m + 1)) → Fin (m + 1) → ℕ :=
        fun y ↦
          multinomialCount
            (fun j : Fin (∑ i, k i) ↦ fun y' : Fin (∑ i, k i) → Fin (m + 1) ↦ y' j) y
      have hprefix_aemeas : AEMeasurable prefixTuple P := by
        refine aemeasurable_pi_lambda _ ?_
        intro j
        exact
          (measurable_fullGridLabel u hu h0 h1).aemeasurable.comp_aemeasurable
            (hX_law j).aemeasurable
      have hcount_aemeas : AEMeasurable (fun ω ↦ countMap (prefixTuple ω)) P := by
        exact (measurable_of_finite countMap).aemeasurable.comp_aemeasurable hprefix_aemeas
      simpa [prefixTuple, countMap, Set.preimage] using
        hcount_aemeas.nullMeasurableSet_preimage (measurableSet_singleton k)
  have hameas :
      AEMeasurable (fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i) P := by
    simpa [f] using hnull.aemeasurable
  refine ⟨hameas, ?_⟩
  refine Measure.ext_of_singleton (μ := P.map (fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i))
    (ν := Measure.pi (fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))) ?_
  intro k
  rw [Measure.map_apply_of_aemeasurable hameas (measurableSet_singleton k)]
  rw [fullGridCount_preimage_singleton_eq_multinomial_mul_poisson P α L X u hu h0 h1 hL
    hLX_indep hX_iid hX1_law]
  rw [Measure.pi_singleton]
  exact poissonMultinomialMass_eq_prodPoissonMass (α := α) (fullGridLabelPMF u hu h0 h1) k

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: each successor cell count in `fullGridCount` is exactly the
corresponding process increment. -/
theorem fullGridCountSuccEqIncrement {m : ℕ}
    (u : Fin (m + 1) → I) (hu : Monotone u) (h1 : u (Fin.last m) = 1) (i : Fin m) (ω : Ω) :
    fullGridCount u h1 L X ω i.succ =
      poissonizedUniformCountingProcess L X (u i.succ) ω -
        poissonizedUniformCountingProcess L X (u i.castSucc) ω := by
  have hIcc :
      Finset.Icc 1 (L ω) =
        (Finset.range (L ω)).map
          ⟨fun j : ℕ ↦ j + 1, by
            intro a b hab
            exact Nat.succ.inj hab⟩ := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · intro hn
      refine ⟨n - 1, by omega, by omega⟩
    · rintro ⟨j, hj, rfl⟩
      omega
  have hlabel :
      ∀ j : ℕ,
        fullGridLabel u h1 (X (j + 1) ω) = i.succ ↔
          u i.castSucc < X (j + 1) ω ∧ X (j + 1) ω ≤ u i.succ := by
    intro j
    constructor
    · intro hx
      simpa [Set.mem_Ioc] using fullGridLabel_mem_Ioc_of_eq_succ u hu h1 i hx
    · intro hx
      exact fullGridLabel_eq_succ_of_mem_Ioc u hu h1 i hx
  calc
    fullGridCount u h1 L X ω i.succ
        = ∑ j ∈ Finset.range (L ω),
            if fullGridLabel u h1 (X (j + 1) ω) = i.succ then 1 else 0 := by
            rw [fullGridCount, multinomialCount]
            have hmap :
                (Finset.univ.filter
                    (fun j : Fin (L ω) =>
                      fullGridLabel u h1 (X (j + 1) ω) = i.succ)).map Fin.valEmbedding
                  =
                  (Finset.range (L ω)).filter
                    (fun j : ℕ => fullGridLabel u h1 (X (j + 1) ω) = i.succ) := by
              ext j
              simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
                Finset.mem_range]
              constructor
              · rintro ⟨a, ha, rfl⟩
                exact ⟨a.2, ha⟩
              · rintro ⟨hj, hjlabel⟩
                exact ⟨⟨j, hj⟩, hjlabel, rfl⟩
            calc
              (Finset.univ.filter
                  (fun j : Fin (L ω) =>
                    fullGridLabel u h1 (X (j + 1) ω) = i.succ)).card
                  =
                  ((Finset.univ.filter
                    (fun j : Fin (L ω) =>
                      fullGridLabel u h1 (X (j + 1) ω) = i.succ)).map
                        Fin.valEmbedding).card := by
                    rw [Finset.card_map]
              _ =
                  ((Finset.range (L ω)).filter
                    (fun j : ℕ => fullGridLabel u h1 (X (j + 1) ω) = i.succ)).card := by
                    rw [hmap]
              _ = ∑ j ∈ Finset.range (L ω),
                    if fullGridLabel u h1 (X (j + 1) ω) = i.succ then 1 else 0 := by
                    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ j ∈ Finset.range (L ω),
          if u i.castSucc < X (j + 1) ω ∧ X (j + 1) ω ≤ u i.succ then 1 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp [hlabel j]
    _ = ∑ j ∈ Finset.Icc 1 (L ω),
          if u i.castSucc < X j ω ∧ X j ω ≤ u i.succ then 1 else 0 := by
            rw [hIcc, Finset.sum_map]
            refine Finset.sum_congr rfl ?_
            intro j hj
            simp
    _ = poissonizedUniformCountingProcess L X (u i.succ) ω -
          poissonizedUniformCountingProcess L X (u i.castSucc) ω := by
            symm
            rw [poissonizedUniformCountingProcess_increment_eq_interval_count L X
              (hu (Fin.castSucc_le_succ i)) ω]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the Poisson rate attached to a successor grid cell is exactly the
length of that half-open interval in `I`. -/
theorem fullGridLabelRateSuccEqIntervalLength {m : ℕ}
    (u : Fin (m + 1) → I) (hu : Monotone u) (h0 : u 0 = 0) (h1 : u (Fin.last m) = 1) (i : Fin m) :
    (fullGridLabelPMF u hu h0 h1 i.succ).toNNReal =
      Real.toNNReal ((u i.succ : ℝ) - (u i.castSucc : ℝ)) := by
  -- Proof comment: the successor mass is the volume of the corresponding half-open interval in
  -- `I`, and `unitInterval.volume_Ioc` computes that volume as the interval length.
  rw [fullGridLabel_toPMF_apply_succ u hu h0 h1 i]
  have hnonneg : 0 ≤ (u i.succ : ℝ) - (u i.castSucc : ℝ) := by
    exact sub_nonneg.mpr (show (u i.castSucc : ℝ) ≤ u i.succ by exact hu (Fin.castSucc_le_succ i))
  rw [unitInterval.volume_Ioc]
  rw [ENNReal.ofReal_eq_coe_nnreal hnonneg]
  simp [Real.toNNReal_of_nonneg hnonneg]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: adjoining the endpoints `0` and `1` to a finite monotone grid in `I`
produces a longer monotone grid whose interior successor cells are the original increments. -/
def endpointAugmentedGrid {n : ℕ} (t : Fin (n + 1) → I) : Fin (n + 3) → I :=
  Fin.snoc (Fin.cons 0 t) 1

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the endpoint-augmented grid starts at `0`. -/
theorem endpointAugmentedGrid_zero {n : ℕ} (t : Fin (n + 1) → I) :
    endpointAugmentedGrid t 0 = 0 := by
  simp [endpointAugmentedGrid]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the endpoint-augmented grid ends at `1`. -/
theorem endpointAugmentedGrid_last {n : ℕ} (t : Fin (n + 1) → I) :
    endpointAugmentedGrid t (Fin.last (n + 2)) = 1 := by
  simp [endpointAugmentedGrid]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the successor interior points of `endpointAugmentedGrid t` are the
successor points of the original grid. -/
theorem endpointAugmentedGrid_succ_succ {n : ℕ} (t : Fin (n + 1) → I) (i : Fin n) :
    endpointAugmentedGrid t (i.castSucc.succ.succ) = t i.succ := by
  unfold endpointAugmentedGrid
  rw [Fin.succ_castSucc, Fin.succ_castSucc, Fin.snoc_castSucc, Fin.cons_succ]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: the predecessor interior points of `endpointAugmentedGrid t` are the
predecessor points of the original grid. -/
theorem endpointAugmentedGrid_castSucc_succ {n : ℕ} (t : Fin (n + 1) → I) (i : Fin n) :
    endpointAugmentedGrid t (i.castSucc.castSucc.succ) = t i.castSucc := by
  unfold endpointAugmentedGrid
  rw [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.cons_succ]

omit [MeasurableSpace Ω] in
/-- Helper for Theorem 5.35: adjoining the endpoints preserves monotonicity of the grid. -/
theorem endpointAugmentedGrid_mono {n : ℕ} (t : Fin (n + 1) → I) (ht : Monotone t) :
    Monotone (endpointAugmentedGrid t) := by
  refine (Fin.monotone_iff_le_succ (f := endpointAugmentedGrid t)).2 ?_
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa [endpointAugmentedGrid] using (t (Fin.last n)).2.2
  | cast j =>
      cases j using Fin.cases with
      | zero =>
          simp [endpointAugmentedGrid]
      | succ j =>
          have hj : t j.castSucc ≤ t j.succ := ht (Fin.castSucc_le_succ j)
          have hleft :
              endpointAugmentedGrid t j.succ.castSucc.castSucc =
                endpointAugmentedGrid t j.castSucc.castSucc.succ := by
            have hidx : j.succ.castSucc.castSucc = j.castSucc.castSucc.succ := by
              ext
              simp
            exact congrArg (endpointAugmentedGrid t) hidx
          have hright :
              endpointAugmentedGrid t j.succ.castSucc.succ =
                endpointAugmentedGrid t j.castSucc.succ.succ := by
            have hidx : j.succ.castSucc.succ = j.castSucc.succ.succ := by
              ext
              simp
            exact congrArg (endpointAugmentedGrid t) hidx
          rw [hleft, hright, endpointAugmentedGrid_castSucc_succ, endpointAugmentedGrid_succ_succ]
          exact hj

omit [IsProbabilityMeasure P] in
/-- Theorem 5.35: if `L` has Poisson law with parameter `α`, the marks `X₁, X₂, …` are i.i.d.
uniform on `[0,1]`, and `L` is independent of the whole mark sequence, then the counting family
`t ↦ #{l ≤ L : 0 < X_l ≤ t}` satisfies on `[0,1]` the source-facing counting-process conditions
corresponding to the chapter's canonical Poisson-process owner abstraction: it starts at `0`, is
nondecreasing, has independent increments, and its interval increments have the expected Poisson
laws. -/
theorem poissonized_uniform_counting_process_is_poisson_process_on_unit_interval
    (hL : HasLaw L (poissonMeasure α) P)
    (hLX_indep : IndepFun L (fun ω ↦ fun n : ℕ ↦ X (n + 1) ω) P)
    (hX_iid : IsIID (fun n ↦ X (n + 1)) P)
    (hX1_law : HasLaw (X 1) (volume : Measure I) P) :
    let N := poissonizedUniformCountingProcess L X
    N 0 = 0 ∧
      Monotone N ∧
      HasIndepIncrements N P ∧
      ∀ ⦃s t : I⦄, s ≤ t →
        HasLaw
          (fun ω ↦ N t ω - N s ω)
          (poissonMeasure (α * Real.toNNReal ((t : ℝ) - (s : ℝ)))) P := by
  haveI : IsProbabilityMeasure P := hL.isProbabilityMeasure
  have hX_indep : iIndepFun (fun n ↦ X (n + 1)) P := hX_iid.iIndepFun
  have hX_law : ∀ n, HasLaw (X (n + 1)) (volume : Measure I) P :=
    iid_uniform_marks_hasLaw P X hX_iid hX1_law
  dsimp
  refine ⟨poissonizedUniformCountingProcess_zero_eq L X,
    poissonizedUniformCountingProcess_mono L X, ?_, ?_⟩
  · -- TODO: use the new singleton-event identity for `fullGridCount` together with the imported
    -- multinomial singleton-mass theorem and the independence of `L` from the labeled mark
    -- sequence to prove the full-grid count vector has product Poisson singleton masses, then
    -- package that discrete product law into `HasIndepIncrements`.
    -- Route correction: the earlier `Fin m`-only partition missed the boundary point `0`, so the
    -- exact identity `sum of cell counts = L` failed pathwise. The new route uses the full-grid
    -- label `fullGridLabel`, with zero fiber `{0}` and successor fibers
    -- `Set.Ioc (u i.castSucc) (u i.succ)`, and that pathwise bridge is now verified in
    -- `fullGridCount_preimage_singleton_eq_length_inter_multinomialCount`.
    intro n t ht
    let u : Fin (n + 3) → I := endpointAugmentedGrid t
    have hu : Monotone u := endpointAugmentedGrid_mono t ht
    have h0 : u 0 = 0 := endpointAugmentedGrid_zero t
    have h1 : u (Fin.last (n + 2)) = 1 := endpointAugmentedGrid_last t
    have hfullLaw :
        HasLaw
          (fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i)
          (Measure.pi (fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))) P :=
      fullGridCountHasLawPiPoisson P α L X u hu h0 h1 hL hLX_indep hX_iid hX1_law
    have hfullIndep :
        iIndepFun (fun i : Fin (n + 3) ↦ fun ω ↦ fullGridCount u h1 L X ω i) P := by
      have hmeas :
          ∀ i : Fin (n + 3), AEMeasurable (fun ω ↦ fullGridCount u h1 L X ω i) P :=
        fun i ↦ (measurable_pi_apply i).aemeasurable.comp_aemeasurable hfullLaw.aemeasurable
      have hcoordLaw :
          ∀ i : Fin (n + 3),
            HasLaw
              (fun ω ↦ fullGridCount u h1 L X ω i)
              (poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal)) P := by
        intro i
        have hevalLaw :
            HasLaw
              (Function.eval i)
              (poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))
              (Measure.pi
                (fun j ↦
                  poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 j).toNNReal))) := by
          exact (measurePreserving_eval
            (fun j ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 j).toNNReal)) i).hasLaw
        simpa [Function.comp] using hevalLaw.fun_comp hfullLaw
      have hcoord_fun :
          (fun i : Fin (n + 3) ↦ Measure.map (fun ω ↦ fullGridCount u h1 L X ω i) P) =
            fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal) := by
        funext i
        exact (hcoordLaw i).map_eq
      refine (iIndepFun_iff_map_fun_eq_pi_map hmeas).2 ?_
      simpa [hcoord_fun] using hfullLaw.map_eq
    have hsel_inj :
        Function.Injective (fun i : Fin n ↦ ((i.succ.castSucc).succ : Fin (n + 3))) := by
      intro a b hab
      exact Fin.ext <| by simpa using congrArg Fin.val hab
    have hselected :
        iIndepFun
          (fun i : Fin n ↦ fun ω ↦ fullGridCount u h1 L X ω ((i.succ.castSucc).succ)) P :=
      hfullIndep.precomp hsel_inj
    have hEq :
        (fun i : Fin n ↦ fun ω ↦ fullGridCount u h1 L X ω ((i.succ.castSucc).succ)) =
          fun i ω ↦
            poissonizedUniformCountingProcess L X (t i.succ) ω -
              poissonizedUniformCountingProcess L X (t i.castSucc) ω := by
      funext i ω
      simpa [u, endpointAugmentedGrid_succ_succ, endpointAugmentedGrid_castSucc_succ] using
        fullGridCountSuccEqIncrement L X u hu h1 i.succ.castSucc ω
    refine hselected.congr ?_
    intro i
    exact Filter.EventuallyEq.of_eq (by simpa using congrArg (fun f ↦ f i) hEq)
  · intro s t hst
    let middleGrid : Fin 2 → I := Fin.cons s (fun _ ↦ t)
    let u : Fin 4 → I := endpointAugmentedGrid middleGrid
    have hu : Monotone u := endpointAugmentedGrid_mono middleGrid (by
      refine (Fin.monotone_iff_le_succ (f := middleGrid)).2 ?_
      intro i
      fin_cases i
      simpa [middleGrid] using hst)
    have h0 : u 0 = 0 := endpointAugmentedGrid_zero middleGrid
    have h1 : u (Fin.last 3) = 1 := endpointAugmentedGrid_last middleGrid
    let middle : Fin 3 := ⟨1, by decide⟩
    have hfullLaw :
        HasLaw
          (fun ω ↦ fun i ↦ fullGridCount u h1 L X ω i)
          (Measure.pi (fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))) P :=
      fullGridCountHasLawPiPoisson P α L X u hu h0 h1 hL hLX_indep hX_iid hX1_law
    have hcoordLaw :
        HasLaw
          (fun ω ↦ fullGridCount u h1 L X ω middle.succ)
          (poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 middle.succ).toNNReal)) P := by
      have hevalLaw :
          HasLaw
            (Function.eval middle.succ)
            (poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 middle.succ).toNNReal))
            (Measure.pi
              (fun i ↦
                poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))) := by
        exact (measurePreserving_eval
          (fun i ↦ poissonMeasure (α * (fullGridLabelPMF u hu h0 h1 i).toNNReal))
          middle.succ).hasLaw
      simpa [Function.comp] using hevalLaw.fun_comp hfullLaw
    have hEq :
        (fun ω ↦ fullGridCount u h1 L X ω middle.succ) =
          fun ω ↦ poissonizedUniformCountingProcess L X t ω -
            poissonizedUniformCountingProcess L X s ω := by
      funext ω
      simpa [u, middleGrid, middle, endpointAugmentedGrid_succ_succ,
        endpointAugmentedGrid_castSucc_succ] using
        fullGridCountSuccEqIncrement L X u hu h1 middle ω
    have hrate :
        (fullGridLabelPMF u hu h0 h1 middle.succ).toNNReal =
          Real.toNNReal ((t : ℝ) - (s : ℝ)) := by
      simpa [u, middleGrid, middle, endpointAugmentedGrid_succ_succ,
        endpointAugmentedGrid_castSucc_succ] using
        fullGridLabelRateSuccEqIntervalLength u hu h0 h1 middle
    simpa [hEq, hrate] using hcoordLaw.congr (Filter.EventuallyEq.of_eq hEq.symm)

end

end
