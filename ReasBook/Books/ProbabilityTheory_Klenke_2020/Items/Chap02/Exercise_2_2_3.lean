/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

variable {Ω : Type u} {m n : ℕ}

/-- The count vector recording how often each value in `Fin m` appears among the samples
`X 0 ω, …, X (n - 1) ω`. -/
def multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) : Fin m → ℕ :=
  fun i ↦ Finset.card <| Finset.univ.filter fun j ↦ X j ω = i

/-- The entries of the count vector sum to the sample size. -/
theorem sum_multinomialCount (X : Fin n → Ω → Fin m) (ω : Ω) :
    ∑ i, multinomialCount X ω i = n := by
  let f : Fin n → Fin m := fun j ↦ X j ω
  have h_mapsTo :
      ((Finset.univ : Finset (Fin n)) : Set (Fin n)).MapsTo f (Finset.univ : Finset (Fin m)) :=
    fun _ _ ↦ Finset.mem_univ _
  simpa [multinomialCount] using
    (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm

section

variable [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Helper for Exercise 2.2.3: `tupleCount x` is the deterministic histogram of a word
`x : Fin n → Fin m`. -/
private def tupleCount (x : Fin n → Fin m) : Fin m → ℕ :=
  multinomialCount (fun j ↦ fun y : Fin n → Fin m ↦ y j) x

/-- Helper for Exercise 2.2.3: the deterministic histogram of a word is the multiplicity function of
its associated list. -/
private theorem tupleCount_eq_listCount (x : Fin n → Fin m) (i : Fin m) :
    tupleCount x i = (List.ofFn x).count i := by
  -- Proof comment: rewrite the histogram as a cardinality of coordinate fibers, then use the
  -- standard `Fin` lemma relating that cardinality to the count of `i` in the word list.
  simpa [tupleCount, multinomialCount] using
    Fin.card_filter_univ_eq_vector_get_eq_count i (List.Vector.ofFn x)

/-- Helper for Exercise 2.2.3: the joint law of the sampled word is the finite product measure of
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

/-- Helper for Exercise 2.2.3: a single word has the expected iid product mass. -/
private theorem sampleVecPointMass_eq_prod
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (x : Fin n → Fin m) :
    μ.map (fun ω i ↦ X i ω) ({x} : Set (Fin n → Fin m)) = ∏ j, p (x j) := by
  -- Proof comment: evaluate the pushforward measure on the singleton `{x}` and use the product
  -- measure formula for singleton rectangles.
  rw [sampleVecMap_eq_productMeasure p X h_indep h_law, Measure.pi_singleton]
  simp

/-- Helper for Exercise 2.2.3: if a word has histogram `k`, then its iid product weight depends
only on `k`. -/
private theorem sampleWordWeight_eq_prodPow_of_tupleCount_eq
    (p : PMF (Fin m)) (x : Fin n → Fin m) (k : Fin m → ℕ) (hx : tupleCount x = k) :
    ∏ j, p (x j) = ∏ i, (p i) ^ k i := by
  -- Proof comment: rewrite the word weight as the product over the multiset of letters, then group
  -- equal letters together and replace their multiplicities by the prescribed histogram `k`.
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

/-- Helper for Exercise 2.2.3: every admissible count vector is realized by at least one word of
length `n`. -/
private theorem exists_word_with_tupleCount (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    ∃ x : Fin n → Fin m, tupleCount x = k := by
  classical
  let s : Sym (Fin m) n := (Sym.equivNatSumOfFintype (Fin m) n).symm ⟨k, hk⟩
  let v : List.Vector (Fin m) n :=
    ⟨(s : Multiset (Fin m)).toList, by simp [Sym.card_coe]⟩
  refine ⟨v.get, ?_⟩
  ext i
  -- Proof comment: choose the canonical list representative of the symmetric word attached to `k`;
  -- its multiplicity function is exactly `k`.
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

/-- Helper for Exercise 2.2.3: the type synonym `((Equiv.Perm (Fin n))ᵈᵐᵃ)` is finite because it
is equivalent to `Equiv.Perm (Fin n)`. -/
private instance fintypeDomMulActPermFin : Fintype ((Equiv.Perm (Fin n))ᵈᵐᵃ) :=
  Fintype.ofEquiv (Equiv.Perm (Fin n)) DomMulAct.mk

/-- Helper for Exercise 2.2.3: the histogram entry `tupleCount x i` is the cardinality of the
fiber `{j // x j = i}`. -/
private theorem fintypeCard_fiber_eq_tupleCount (x : Fin n → Fin m) (i : Fin m) :
    Fintype.card {j // x j = i} = tupleCount x i := by
  -- Proof comment: identify the fiber subtype with the filtered universal finset used in the
  -- definition of `tupleCount`.
  rw [Fintype.card_of_subtype (s := Finset.univ.filter fun j : Fin n ↦ x j = i)]
  · simp [tupleCount, multinomialCount]
  · intro j
    simp

/-- Helper for Exercise 2.2.3: if a color does not appear in a word, then its histogram entry is
zero. -/
private theorem tupleCount_eq_zero_of_not_mem_image (x : Fin n → Fin m) {i : Fin m}
    (hi : i ∉ Finset.univ.image x) :
    tupleCount x i = 0 := by
  -- Proof comment: rewrite the histogram entry as a list count and use that `i` is absent from the
  -- word exactly when it is absent from the image of `x`.
  rw [tupleCount_eq_listCount]
  apply List.count_eq_zero_of_not_mem
  simpa [List.mem_ofFn', Set.mem_range, Finset.mem_image] using hi

/-- Helper for Exercise 2.2.3: coordinate permutations preserve the histogram `tupleCount`. -/
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

/-- Helper for Exercise 2.2.3: words with the same histogram differ by a permutation of their
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
    simpa using congrArg Subtype.val ((e (x j)).left_inv ⟨j, rfl⟩)
  have hRight : Function.RightInverse σInv σFun := by
    intro j
    -- Proof comment: the same fiberwise inverse argument proves the opposite composition is the
    -- identity as well.
    rw [hσFun_eq (((e (x₀ j)).symm ⟨j, rfl⟩).2)]
    simpa using congrArg Subtype.val (((e (x₀ j)).symm).left_inv ⟨j, rfl⟩)
  let σ : Equiv.Perm (Fin n) :=
    ⟨σFun, σInv, hLeft, hRight⟩
  refine MulAction.mem_orbit_iff.mpr ?_
  refine ⟨DomMulAct.mk σ, ?_⟩
  ext j
  -- Proof comment: the assembled permutation sends each coordinate of `x` to a coordinate of
  -- `x₀` carrying the same color.
  simpa [σ, σFun, DomMulAct.smul_apply] using congrArg Fin.val ((e (x j) ⟨j, rfl⟩).2)

/-- Helper for Exercise 2.2.3: the stabilizer of a word under coordinate permutations has
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
    let eStab :
        ↥(MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x) ≃
          {g : Equiv.Perm (Fin n) // x ∘ g = x} :=
      DomMulAct.mk.symm.subtypeEquiv
        (fun g ↦ (DomMulAct.mem_stabilizer_iff (f := x) (g := g)))
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eStab, Nat.card_eq_fintype_card]
    simpa [fintypeCard_fiber_eq_tupleCount] using (DomMulAct.stabilizer_card' (f := x))
  calc
    Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x) =
        ∏ i ∈ Finset.univ.image x, Nat.factorial (tupleCount x i) := hcard
    _ = ∏ i, Nat.factorial (tupleCount x i) := by
      -- Proof comment: colors outside the image contribute `0! = 1`, so the product can be
      -- extended from the image of `x` to all colors.
      exact Finset.prod_subset (by simp) fun i _ hi ↦ by
        simp [tupleCount_eq_zero_of_not_mem_image x hi]

/-- Helper for Exercise 2.2.3: the orbit of a word with histogram `k` has cardinality equal to the
multinomial coefficient `Nat.multinomial Finset.univ k`. -/
private theorem card_coordinatePermutationOrbit_eq_multinomial
    (x₀ : Fin n → Fin m) (k : Fin m → ℕ) (hx₀ : tupleCount x₀ = k) :
    Nat.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) = Nat.multinomial Finset.univ k := by
  classical
  have hk_sum : ∑ i, k i = n := by
    -- Proof comment: the total of the histogram of any word is the word length `n`.
    calc
      ∑ i, k i = ∑ i, tupleCount x₀ i := by simpa [hx₀]
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
      Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) *
          ∏ i, Nat.factorial (tupleCount x₀ i) = Nat.factorial n := by
    -- Proof comment: orbit-stabilizer converts the orbit size into the group cardinal divided by
    -- the stabilizer size, and the acting group is the full permutation group on `Fin n`.
    calc
      Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) *
            ∏ i, Nat.factorial (tupleCount x₀ i)
          = Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) *
              Fintype.card (MulAction.stabilizer ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) := by
            rw [coordinatePermutationStabilizerCard_eq_prodFactorial]
      _ = Fintype.card ((Equiv.Perm (Fin n))ᵈᵐᵃ) := by
            exact MulAction.card_orbit_mul_card_stabilizer_eq_card_group
              (α := ((Equiv.Perm (Fin n))ᵈᵐᵃ)) (b := x₀)
      _ = Nat.factorial n := hgroup
  have hmultinomial :
      Nat.multinomial Finset.univ k * ∏ i, Nat.factorial (tupleCount x₀ i) = Nat.factorial n := by
    -- Proof comment: this is exactly the standard multinomial identity after rewriting the
    -- histogram of `x₀` as `k`.
    rw [show (∏ i, Nat.factorial (tupleCount x₀ i)) = ∏ i, Nat.factorial (k i) by simpa [hx₀]]
    rw [mul_comm]
    simpa [hk_sum] using (Nat.multinomial_spec (s := Finset.univ) (f := k))
  have hpos : 0 < ∏ i, Nat.factorial (tupleCount x₀ i) := by
    -- Proof comment: factorials are positive, so the common factor can be cancelled.
    exact Finset.prod_pos fun i _ ↦ Nat.factorial_pos _
  have horbitCard :
      Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) =
        Nat.multinomial Finset.univ k :=
    Nat.mul_right_cancel hpos (horbit.trans hmultinomial.symm)
  simpa [Nat.card_eq_fintype_card] using horbitCard

/-- Exercise 2.2.3: if `X : Fin n → Ω → Fin m` is an independent family with common law `p`,
then the count vector `ω ↦ (fun i ↦ #{j | X j ω = i})` has multinomial point mass
`Nat.multinomial Finset.univ k * ∏ i, p i ^ k i` at every
`k ∈ Finset.piAntidiag Finset.univ n`. -/
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
    -- Proof comment: after the event rewrite above, pass from the original probability space to the
    -- finite word space by the pushforward measure of `sampleVec`.
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
        Finset.sum orbitFinset fun x ↦ (μ.map sampleVec).toPMF x := by
    -- Proof comment: once the histogram class is identified with the orbit, the finite-space mass
    -- is the sum of the point masses over that orbit.
    simpa [h_countClass_eq_orbit, orbitFinset] using
      ((μ.map sampleVec).toPMF.toMeasure_apply_finset orbitFinset)
  calc
    μ (multinomialCount X ⁻¹' {k})
        = (μ.map sampleVec) {x | tupleCount x = k} := h_push
    _ = Finset.sum orbitFinset fun x ↦ (μ.map sampleVec).toPMF x := h_mass_sum
    _ = Finset.sum orbitFinset fun _x ↦ ∏ i, (p i) ^ k i := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      apply h_common_weight
      exact
        (tupleCount_eq_of_mem_coordinatePermutationOrbit x x₀ (by
          simpa [orbitFinset] using hx)).trans hx₀
    _ = ((orbitFinset.card : ℕ) : ENNReal) *
          ∏ i, (p i) ^ k i := by
      simp [nsmul_eq_mul]
    _ = (Fintype.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) : ENNReal) *
          ∏ i, (p i) ^ k i := by
      simpa [orbitFinset] using
        congrArg (fun t : ℕ => (t : ENNReal))
          (Set.Finite.card_toFinset
            (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀).toFinite)
    _ = ((Nat.card (MulAction.orbit ((Equiv.Perm (Fin n))ᵈᵐᵃ) x₀) : ℕ) : ENNReal) *
          ∏ i, (p i) ^ k i := by
      rw [← Nat.card_eq_fintype_card]
    _ = (Nat.multinomial Finset.univ k : ENNReal) * ∏ i, (p i) ^ k i := by
      exact congrArg (fun t : ℕ => (t : ENNReal) * ∏ i, (p i) ^ k i)
        (card_coordinatePermutationOrbit_eq_multinomial x₀ k hx₀)

/-- Source-style reformulation of Exercise 2.2.3 with the total-count hypothesis written as
`∑ i, k i = n`. -/
theorem multinomialCount_preimage_singleton_eq_multinomial_of_sum_eq
    (p : PMF (Fin m)) (X : Fin n → Ω → Fin m) (h_indep : iIndepFun X μ)
    (h_law : ∀ i, HasLaw (X i) p.toMeasure μ) (k : Fin m → ℕ) (hk : ∑ i, k i = n) :
    μ (multinomialCount X ⁻¹' {k}) =
      (Nat.multinomial Finset.univ k : ENNReal) * (∏ i, (p i) ^ k i) := by
  simpa [Finset.mem_piAntidiag, hk] using
    multinomialCount_preimage_singleton_eq_multinomial p X h_indep h_law k

end
