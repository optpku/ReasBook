/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib.Analysis.SpecialFunctions.Choose
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Gamma
import Books.ProbabilityTheory_Klenke_2020.Items.Chap15.Theorem_15_37

-- Declarations for this item will be appended below by the statement pipeline.

open Filter MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

noncomputable section

universe u v

variable {Ω : Type u} {Ω' : Type v} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
variable {X : ℕ → Ω → ℝ} {Y : Ω' → ℝ}

/-- Helper for Exercise 15.4.6: `tupleMultiplicity u i` counts how many coordinates of the finite
word `u : Fin m → Fin n` are equal to `i`. -/
def tupleMultiplicity {m n : ℕ} (u : Fin m → Fin n) (i : Fin n) : ℕ :=
  ((Finset.univ : Finset (Fin m)).filter fun j ↦ u j = i).card

/-- Helper for Exercise 15.4.6: the multiplicities of a finite word sum to its length. -/
lemma sum_tupleMultiplicity {m n : ℕ} (u : Fin m → Fin n) :
    ∑ i : Fin n, tupleMultiplicity u i = m := by
  classical
  let f : Fin m → Fin n := u
  have h_mapsTo :
      ((Finset.univ : Finset (Fin m)) : Set (Fin m)).MapsTo f
        (Finset.univ : Finset (Fin n)) := by
    intro j hj
    simp
  -- Count the domain by summing the fiber cardinalities of `u`.
  simpa [f, tupleMultiplicity] using
    (Finset.card_eq_sum_card_fiberwise h_mapsTo).symm

/-- Helper for Exercise 15.4.6: the filtered-cardinality definition of `tupleMultiplicity`
matches the subtype fiber cardinality used by mathlib's fiberwise product lemmas. -/
lemma tupleMultiplicity_eq_fiberCard {m n : ℕ} (u : Fin m → Fin n) (i : Fin n) :
    tupleMultiplicity u i = Fintype.card {j // u j = i} := by
  classical
  -- Proof comment: `Fintype.card_subtype` rewrites the subtype cardinality into the same filter
  -- on `Finset.univ` used by `tupleMultiplicity`.
  rw [tupleMultiplicity, Fintype.card_subtype]

/-- Helper for Exercise 15.4.6: regrouping a tuple product by the fibers of the indexing word
turns it into a product of powers. -/
lemma prod_apply_eq_prod_pow_tupleMultiplicity {R : Type*} [CommSemiring R]
    {m n : ℕ} (u : Fin m → Fin n) (x : Fin n → R) :
    (∏ j : Fin m, x (u j)) = ∏ i : Fin n, x i ^ tupleMultiplicity u i := by
  classical
  -- Proof comment: switch once to the subtype-fiber cardinality normal form used by
  -- `Fintype.prod_fiberwise'`, then rewrite those exponents back to `tupleMultiplicity`.
  simpa [tupleMultiplicity_eq_fiberCard] using (Fintype.prod_fiberwise' u x).symm

/-- Helper for Exercise 15.4.6: the mixed moment attached to a finite word factors through the
coordinate moments indexed by its multiplicities. -/
lemma tupleMoment_eq_prodIntegrals
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    {m n : ℕ} (u : Fin m → Fin n) :
    ∫ ω, ∏ j : Fin m, X (u j) ω ∂P =
      ∏ i : Fin n, ∫ ω, X i ω ^ tupleMultiplicity u i ∂P := by
  let Xfin : Fin n → Ω → ℝ := fun i ↦ X i
  have hindepFin : iIndepFun Xfin P := hindep.precomp Fin.val_injective
  have hmeas : ∀ i : Fin n, AEMeasurable (Xfin i) P := fun i ↦ (hident i).aemeasurable_fst
  have hpowMeas :
      ∀ i : Fin n,
        AEStronglyMeasurable (fun x : ℝ ↦ x ^ tupleMultiplicity u i) (P.map (Xfin i)) := by
    intro i
    exact (continuous_pow _).aestronglyMeasurable
  -- Proof comment: rewrite the tuple product as a product over distinct coordinates and then use
  -- independence of the restricted `Fin n` family.
  calc
    ∫ ω, ∏ j : Fin m, X (u j) ω ∂P =
        ∫ ω, ∏ i : Fin n, X i ω ^ tupleMultiplicity u i ∂P := by
          refine integral_congr_ae ?_
          filter_upwards with ω
          simpa using prod_apply_eq_prod_pow_tupleMultiplicity u (fun i ↦ X i ω)
    _ = ∏ i : Fin n, ∫ ω, X i ω ^ tupleMultiplicity u i ∂P := by
          simpa [Xfin] using hindepFin.integral_fun_prod_comp
            (X := Xfin) hmeas hpowMeas

/-- Helper for Exercise 15.4.6: if one coordinate appears exactly once in a tuple word, the
corresponding centered mixed moment vanishes. -/
lemma tupleMoment_eq_zero_of_tupleMultiplicity_eq_one
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    {m n : ℕ} (u : Fin m → Fin n) {i : Fin n}
    (hi : tupleMultiplicity u i = 1) :
    ∫ ω, ∏ j : Fin m, X (u j) ω ∂P = 0 := by
  have hfactor := tupleMoment_eq_prodIntegrals (X := X) (P := P) hindep hident u
  have hsingle :
      ∫ ω, X i ω ^ tupleMultiplicity u i ∂P = 0 := by
    -- Proof comment: the singled-out coordinate has first moment `0` by identical distribution.
    calc
      ∫ ω, X i ω ^ tupleMultiplicity u i ∂P = ∫ ω, X i ω ∂P := by
        simpa [hi]
      _ = ∫ ω, X 0 ω ∂P := by
        simpa using ((hident i).integral_eq)
      _ = 0 := h0
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := by
    simp
  -- Proof comment: once the `i`-factor is zero, the whole finite product is zero.
  calc
    ∫ ω, ∏ j : Fin m, X (u j) ω ∂P
      = ∏ j : Fin n, ∫ ω, X j ω ^ tupleMultiplicity u j ∂P := hfactor
    _ = 0 := by
          exact Finset.prod_eq_zero_iff.2 ⟨i, hi_mem, hsingle⟩

/-- Helper for Exercise 15.4.6: if no tuple multiplicity is equal to `1`, then at most half of
the tuple length can be occupied by distinct coordinates. -/
lemma two_mul_card_nonzero_tupleMultiplicity_le
    {m n : ℕ} (u : Fin m → Fin n)
    (h_no_one : ∀ i : Fin n, tupleMultiplicity u i ≠ 1) :
    2 * (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card ≤ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0
  have hs_le_sum : 2 * s.card ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := by
    -- Proof comment: every multiplicity on the support is at least `2` because `0` and `1` are
    -- both excluded there.
    calc
      2 * s.card = Finset.sum s (fun _ : Fin n ↦ 2) := by
        simp [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi0 : tupleMultiplicity u i ≠ 0 := by
          simpa [s] using (Finset.mem_filter.mp hi).2
        have hpos : 0 < tupleMultiplicity u i := Nat.pos_of_ne_zero hi0
        have hne1 : tupleMultiplicity u i ≠ 1 := h_no_one i
        omega
  have hs_sum : Finset.sum s (fun i ↦ tupleMultiplicity u i) = ∑ i : Fin n, tupleMultiplicity u i := by
    -- Proof comment: outside the support the multiplicity is zero, so restricting the sum does
    -- not change its value.
    rw [show s = Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0 by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi0 : tupleMultiplicity u i = 0
    · simp [hi0]
    · simp [hi0]
  calc
    2 * (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card = 2 * s.card := by
      rfl
    _ ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := hs_le_sum
    _ = ∑ i : Fin n, tupleMultiplicity u i := hs_sum
    _ = m := sum_tupleMultiplicity u

/-- Helper for Exercise 15.4.6: a power of the partial sum can be regrouped by multinomial
profiles on `Finset.range n`. -/
lemma partialSumPow_eq_sum_piAntidiag {m n : ℕ} (ω : Ω) :
    (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m =
      ∑ a ∈ Finset.piAntidiag (Finset.range n) m,
        (Nat.multinomial (Finset.range n) a : ℝ) *
          Finset.prod (Finset.range n) (fun i ↦ X i ω ^ a i) := by
  -- Proof comment: use the canonical multinomial expansion rather than the earlier tuple-word
  -- normalization.
  simpa using
    (Finset.sum_pow_eq_sum_piAntidiag (s := Finset.range n) (f := fun i ↦ X i ω) m)

/-- Helper for Exercise 15.4.6: rewrite the `Finset.range` partial sum as a sum over
`Fin n`. -/
lemma partialSum_eq_sum_univ_fin {n : ℕ} (ω : Ω) :
    Finset.sum (Finset.range n) (fun i ↦ X i ω) = ∑ i : Fin n, X i ω := by
  -- Proof comment: switch once to the canonical `Fin n` indexing so later profile lemmas stay in
  -- the same normal form.
  simpa using (Fin.sum_univ_eq_sum_range (f := fun i : ℕ ↦ X i ω) n).symm

/-- Helper for Exercise 15.4.6: a power of the `Fin n` partial sum can be expanded as a sum over
tuple words `u : Fin m → Fin n`. -/
lemma partialSumPow_eq_sum_tupleWords {m n : ℕ} (ω : Ω) :
    (∑ i : Fin n, X i ω) ^ m = ∑ u : Fin m → Fin n, ∏ j : Fin m, X (u j) ω := by
  -- Proof comment: this is the canonical finite-word expansion of a power via
  -- `Finset.sum_pow'` on the `Fin n` index type.
  simpa using (Finset.sum_pow' (s := (Finset.univ : Finset (Fin n))) (f := fun i ↦ X i ω) m)

/-- Helper for Exercise 15.4.6: for a fixed finite support set `s`, the number of tuple words
whose image is contained in `s` is exactly `s.card ^ m`. -/
lemma tupleWordsMapsTo_card {m n : ℕ} (s : Finset (Fin n)) :
    (((Finset.univ : Finset (Fin m → Fin n)).filter fun u => ∀ j : Fin m, u j ∈ s).card =
      s.card ^ m) := by
  classical
  have hfilter :
      ((Finset.univ : Finset (Fin m → Fin n)).filter fun u => ∀ j : Fin m, u j ∈ s) =
        Fintype.piFinset (fun _ : Fin m ↦ s) := by
    ext u
    simp
  rw [hfilter]
  simpa using (Fintype.card_piFinset_const s m)

/-- Helper for Exercise 15.4.6: tuple words with multiplicity support of size at most `r` are
bounded by a fixed constant times `n ^ r`. -/
lemma smallSupportTupleCount_bound {m r : ℕ} (hm : 0 < m) :
    ∃ C : ℕ,
      ∀ n,
        (((Finset.univ : Finset (Fin m → Fin n)).filter
            fun u =>
              (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card ≤ r).card ≤
          C * n ^ r) := by
  classical
  let C : ℕ := ∑ t ∈ Finset.Icc 1 r, t ^ m
  refine ⟨C, ?_⟩
  intro n
  cases n with
  | zero =>
      have hfilter_le :
          (((Finset.univ : Finset (Fin m → Fin 0)).filter
              fun u =>
                (Finset.univ.filter fun i : Fin 0 ↦ tupleMultiplicity u i ≠ 0).card ≤ r).card) ≤ 0 := by
        calc
          (((Finset.univ : Finset (Fin m → Fin 0)).filter
              fun u =>
                (Finset.univ.filter fun i : Fin 0 ↦ tupleMultiplicity u i ≠ 0).card ≤ r).card)
              ≤ (Finset.univ : Finset (Fin m → Fin 0)).card := by
                exact Finset.card_filter_le
                  (s := (Finset.univ : Finset (Fin m → Fin 0)))
                  (p := fun u =>
                    (Finset.univ.filter fun i : Fin 0 ↦ tupleMultiplicity u i ≠ 0).card ≤ r)
          _ = 0 := by
              simp [hm.ne']
      exact le_trans hfilter_le (by simp [C])
  | succ n =>
      let A : Finset (Fin m → Fin (n + 1)) :=
        (Finset.univ : Finset (Fin m → Fin (n + 1))).filter
          fun u =>
            (Finset.univ.filter fun i : Fin (n + 1) ↦ tupleMultiplicity u i ≠ 0).card ≤ r
      let B : Finset (Fin m → Fin (n + 1)) :=
        (Finset.Icc 1 r).biUnion fun t =>
          (((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
            ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦ ∀ j : Fin m, u j ∈ s))
      have hsub : A ⊆ B := by
        intro u hu
        let s : Finset (Fin (n + 1)) :=
          Finset.univ.filter fun i : Fin (n + 1) ↦ tupleMultiplicity u i ≠ 0
        have hs_le_r : s.card ≤ r := by
          simpa [A, s] using (Finset.mem_filter.mp hu).2
        have hs_nonempty : s.Nonempty := by
          let j : Fin m := ⟨0, hm⟩
          refine ⟨u j, ?_⟩
          have hpos : 0 < tupleMultiplicity u (u j) := by
            rw [tupleMultiplicity]
            exact Finset.card_pos.mpr ⟨j, by simp [j]⟩
          simp [s, Nat.ne_of_gt hpos]
        have hs_mem_Icc : s.card ∈ Finset.Icc 1 r := by
          rw [Finset.mem_Icc]
          exact ⟨Finset.one_le_card.mpr hs_nonempty, hs_le_r⟩
        have hs_mem_powerset :
            s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s.card := by
          exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, rfl⟩
        have hmaps : ∀ j : Fin m, u j ∈ s := by
          intro j
          have hpos : 0 < tupleMultiplicity u (u j) := by
            rw [tupleMultiplicity]
            exact Finset.card_pos.mpr ⟨j, by simp⟩
          simp [s, Nat.ne_of_gt hpos]
        -- Proof comment: each admissible word belongs to the support-indexed block determined by
        -- its exact multiplicity support, and `m > 0` rules out the empty-support branch.
        exact Finset.mem_biUnion.2 ⟨s.card, hs_mem_Icc, Finset.mem_biUnion.2 ⟨s, hs_mem_powerset, by
          simp [hmaps]⟩⟩
      have hinner :
          ∀ t ∈ Finset.Icc 1 r,
            ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦
                  ∀ j : Fin m, u j ∈ s)).card) ≤
              ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * t ^ m := by
        intro t ht
        refine Finset.card_biUnion_le_card_mul
          ((Finset.univ : Finset (Fin (n + 1))).powersetCard t)
          (fun s ↦ ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦ ∀ j : Fin m, u j ∈ s))
          (t ^ m) ?_
        intro s hs
        rw [tupleWordsMapsTo_card]
        rw [(Finset.mem_powersetCard.mp hs).2]
      have hsum_le :
          B.card ≤ ∑ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * t ^ m := by
        calc
          B.card ≤ ∑ t ∈ Finset.Icc 1 r,
              ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                  ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦
                    ∀ j : Fin m, u j ∈ s)).card) := by
                simpa [B] using (Finset.card_biUnion_le :
                  ((Finset.Icc 1 r).biUnion fun t =>
                    (((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                      ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦
                        ∀ j : Fin m, u j ∈ s))).card ≤
                    ∑ t ∈ Finset.Icc 1 r,
                      ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                          ((Finset.univ : Finset (Fin m → Fin (n + 1))).filter fun u ↦
                            ∀ j : Fin m, u j ∈ s)).card))
          _ ≤ ∑ t ∈ Finset.Icc 1 r,
              ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * t ^ m := by
                refine Finset.sum_le_sum ?_
                intro t ht
                exact hinner t ht
      have hterm :
          ∀ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * t ^ m ≤
              t ^ m * (n + 1) ^ r := by
        intro t ht
        have ht_le_r : t ≤ r := (Finset.mem_Icc.mp ht).2
        have hchoose :
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card ≤ (n + 1) ^ t := by
          rw [Finset.card_powersetCard]
          simpa using (Nat.choose_le_pow (n + 1) t)
        have hpow : (n + 1) ^ t ≤ (n + 1) ^ r := by
          exact Nat.pow_le_pow_right (Nat.succ_pos _) ht_le_r
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_right (t ^ m) (hchoose.trans hpow)
      -- Proof comment: after covering by support size, the support is chosen in at most `n ^ t`
      -- ways and each chosen support carries exactly `t ^ m` tuple words.
      calc
        A.card ≤ B.card := Finset.card_le_card hsub
        _ ≤ ∑ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * t ^ m := hsum_le
        _ ≤ ∑ t ∈ Finset.Icc 1 r, t ^ m * (n + 1) ^ r := by
              refine Finset.sum_le_sum ?_
              intro t ht
              exact hterm t ht
        _ = C * (n + 1) ^ r := by
              simp [C, Finset.sum_mul]

/-- Helper for Exercise 15.4.6: a power of the `Fin n` partial sum can be regrouped by
multinomial profiles on `Finset.univ`. -/
lemma partialSumPow_eq_sum_piAntidiag_univ {m n : ℕ} (ω : Ω) :
    (∑ i : Fin n, X i ω) ^ m =
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m,
        (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
          (∏ i : Fin n, X i ω ^ a i) := by
  -- Proof comment: this is the canonical multinomial expansion on the `Fin n` index type used by
  -- the profile moment and support-cardinality helpers.
  simpa using
    (Finset.sum_pow_eq_sum_piAntidiag
      (s := (Finset.univ : Finset (Fin n))) (f := fun i ↦ X i ω) m)

/-- Helper for Exercise 15.4.6: a profile-indexed mixed moment factors into the product of the
coordinate moments. -/
lemma profileMoment_eq_prodCoordinateMoments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    {n : ℕ} (a : Fin n → ℕ) :
    ∫ ω, ∏ i : Fin n, X i ω ^ a i ∂P =
      ∏ i : Fin n, ∫ ω, X i ω ^ a i ∂P := by
  let Xfin : Fin n → Ω → ℝ := fun i ↦ X i
  have hindepFin : iIndepFun Xfin P := hindep.precomp Fin.val_injective
  have hmeas : ∀ i : Fin n, AEMeasurable (Xfin i) P := fun i ↦ (hident i).aemeasurable_fst
  have hpowMeas :
      ∀ i : Fin n,
        AEStronglyMeasurable (fun x : ℝ ↦ x ^ a i) (P.map (Xfin i)) := by
    intro i
    exact (continuous_pow _).aestronglyMeasurable
  -- Proof comment: restrict the iid family to `Fin n` and then apply the finite-product integral
  -- factorization from the independence API.
  simpa [Xfin] using hindepFin.integral_fun_prod_comp
    (X := Xfin) hmeas hpowMeas

/-- Helper for Exercise 15.4.6: if a profile has a coordinate with exponent `1`, then the
corresponding mixed moment vanishes because the common mean is `0`. -/
lemma profileMoment_eq_zero_of_hasExponentOne
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    {n : ℕ} (a : Fin n → ℕ) {i : Fin n}
    (hi : a i = 1) :
    ∫ ω, ∏ j : Fin n, X j ω ^ a j ∂P = 0 := by
  have hfactor := profileMoment_eq_prodCoordinateMoments (X := X) (P := P) hindep hident a
  have hsingle : ∫ ω, X i ω ^ a i ∂P = 0 := by
    -- Proof comment: identical distribution transports the centered first moment from `X 0` to
    -- the singled-out coordinate.
    calc
      ∫ ω, X i ω ^ a i ∂P = ∫ ω, X i ω ∂P := by
        simpa [hi]
      _ = ∫ ω, X 0 ω ∂P := by
        simpa using (hident i).integral_eq
      _ = 0 := h0
  have hi_mem : i ∈ (Finset.univ : Finset (Fin n)) := by
    simp
  -- Proof comment: split off the `i`-factor from the product of one-dimensional moments.
  calc
    ∫ ω, ∏ j : Fin n, X j ω ^ a j ∂P = ∏ j : Fin n, ∫ ω, X j ω ^ a j ∂P := hfactor
    _ = 0 := by
          exact Finset.prod_eq_zero_iff.2 ⟨i, hi_mem, hsingle⟩

/-- Helper for Exercise 15.4.6: if every nonzero exponent in a profile is at least `2`, then the
support size is at most half of the total degree. -/
lemma two_mul_card_nonzero_profile_le
    {m n : ℕ} (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i = m)
    (h_no_one : ∀ i : Fin n, a i ≠ 1) :
    2 * (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  have hs_le_sum : 2 * s.card ≤ Finset.sum s a := by
    -- Proof comment: every exponent on the support is at least `2` because the only smaller
    -- nonnegative possibilities are `0` and `1`, both excluded.
    calc
      2 * s.card = Finset.sum s (fun _ : Fin n ↦ 2) := by
        simp [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ Finset.sum s a := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi0 : a i ≠ 0 := by
          simpa [s] using (Finset.mem_filter.mp hi).2
        have hpos : 0 < a i := Nat.pos_of_ne_zero hi0
        have hne1 : a i ≠ 1 := h_no_one i
        omega
  have hs_sum : Finset.sum s a = ∑ i : Fin n, a i := by
    -- Proof comment: outside the support the profile coordinates vanish, so the restricted and
    -- unrestricted sums agree.
    rw [show s = Finset.univ.filter fun i : Fin n ↦ a i ≠ 0 by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi0 : a i = 0
    · simp [hi0]
    · simp [hi0]
  calc
    2 * (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = 2 * s.card := by
      rfl
    _ ≤ Finset.sum s a := hs_le_sum
    _ = ∑ i : Fin n, a i := hs_sum
    _ = m := hsum

/-- Helper for Exercise 15.4.6: the pure pair profile attached to `s` places exponent `2` on `s`
and `0` elsewhere. -/
def pairProfile {n : ℕ} (s : Finset (Fin n)) : Fin n → ℕ :=
  fun i ↦ if i ∈ s then 2 else 0

/-- Helper for Exercise 15.4.6: the mixed moment of a pure pair profile is the `k`th power of the
common second moment. -/
lemma pairProfileMoment_eq_secondMoment_pow
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    {k n : ℕ} {s : Finset (Fin n)}
    (hs : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
    ∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P =
      (∫ ω, X 0 ω ^ 2 ∂P) ^ k := by
  classical
  have hfactor :=
    profileMoment_eq_prodCoordinateMoments (X := X) (P := P) hindep hident (pairProfile s)
  have hprod_pair :
      ∏ i : Fin n, ∫ ω, X i ω ^ pairProfile s i ∂P =
        Finset.prod s (fun i ↦ ∫ ω, X i ω ^ 2 ∂P) := by
    -- Proof comment: only the coordinates in `s` contribute nontrivially, and on `s` the
    -- profile exponent is exactly `2`.
    calc
      ∏ i : Fin n, ∫ ω, X i ω ^ pairProfile s i ∂P
          = ∏ i : Fin n, if i ∈ s then ∫ ω, X i ω ^ 2 ∂P else 1 := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              by_cases hi_mem : i ∈ s
              · simp [pairProfile, hi_mem]
              · simp [pairProfile, hi_mem]
      _ = Finset.prod s (fun i ↦ ∫ ω, X i ω ^ 2 ∂P) := by
            simpa using
              (Finset.prod_ite_mem (s := s) (f := fun i : Fin n ↦ ∫ ω, X i ω ^ 2 ∂P))
  have hconst :
      ∀ i ∈ s, ∫ ω, X i ω ^ 2 ∂P = ∫ ω, X 0 ω ^ 2 ∂P := by
    intro i hi
    have hpowIdent : IdentDistrib (fun ω ↦ X i ω ^ 2) (fun ω ↦ X 0 ω ^ 2) P P :=
      (hident i).comp (measurable_id.pow_const 2)
    simpa [Function.comp] using hpowIdent.integral_eq
  -- Proof comment: after factorization, every surviving second moment is the common second
  -- moment, so the support product becomes a `k`th power.
  calc
    ∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P
        = ∏ i : Fin n, ∫ ω, X i ω ^ pairProfile s i ∂P := hfactor
    _ = Finset.prod s (fun i ↦ ∫ ω, X i ω ^ 2 ∂P) := hprod_pair
    _ = (∫ ω, X 0 ω ^ 2 ∂P) ^ s.card := Finset.prod_eq_pow_card hconst
    _ = (∫ ω, X 0 ω ^ 2 ∂P) ^ k := by rw [(Finset.mem_powersetCard.mp hs).2]

/-- Helper for Exercise 15.4.6: the multinomial coefficient of a pure pair profile is
`(2k)! / 2^k`. -/
lemma pairProfileMultinomial_eq_factorial_div_pow
    {k n : ℕ} {s : Finset (Fin n)}
    (hs : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
    (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) =
      (Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k) := by
  have hsum_pair : ∑ i : Fin n, pairProfile s i = 2 * k := by
    -- Proof comment: the pair profile contributes `2` on the chosen support and `0` elsewhere.
    calc
      ∑ i : Fin n, pairProfile s i = ∑ i : Fin n, if i ∈ s then 2 else 0 := by
        rfl
      _ = Finset.sum s (fun _ : Fin n ↦ (2 : ℕ)) := by
            simpa using (Finset.sum_ite_mem (s := s) (f := fun _ : Fin n ↦ (2 : ℕ)))
      _ = 2 * k := by
            simpa [Nat.mul_comm, (Finset.mem_powersetCard.mp hs).2]
  have hprod_factorial : ∏ i : Fin n, Nat.factorial (pairProfile s i) = 2 ^ k := by
    -- Proof comment: on the support we get the constant factor `2! = 2`, and off the support we
    -- get `0! = 1`.
    have hconst_prod :
        Finset.prod s (fun _ : Fin n ↦ Nat.factorial 2) = Nat.factorial 2 ^ s.card :=
      by simpa using (Finset.prod_const (s := s) (b := Nat.factorial 2))
    calc
      ∏ i : Fin n, Nat.factorial (pairProfile s i)
          = ∏ i : Fin n, if i ∈ s then Nat.factorial 2 else 1 := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              by_cases hi_mem : i ∈ s
              · simp [pairProfile, hi_mem]
              · simp [pairProfile, hi_mem]
      _ = Finset.prod s (fun _ : Fin n ↦ Nat.factorial 2) := by
            simpa using (Finset.prod_ite_mem (s := s) (f := fun _ : Fin n ↦ Nat.factorial 2))
      _ = Nat.factorial 2 ^ s.card := hconst_prod
      _ = 2 ^ k := by
            rw [(Finset.mem_powersetCard.mp hs).2]
            norm_num
  have hnat :
      Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) * 2 ^ k =
        Nat.factorial (2 * k) := by
    simpa [hsum_pair, hprod_factorial, Nat.mul_comm] using
      (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin n))) (f := pairProfile s))
  have hpow_ne : ((2 : ℝ) ^ k) ≠ 0 := by positivity
  have hcast :
      (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) * ((2 : ℝ) ^ k) =
        (Nat.factorial (2 * k) : ℝ) := by
    exact_mod_cast hnat
  apply (eq_div_iff hpow_ne).2
  exact hcast

/-- Helper for Exercise 15.4.6: summing the pure pair profiles over all `k`-subsets produces the
exact leading term in the even moment expansion. -/
lemma pairProfilesContribution_eq_chooseMainTerm
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    {k n : ℕ} :
    ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k,
      (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
        (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P)
      = (((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
          (∫ ω, X 0 ω ^ 2 ∂P) ^ k) * (n.choose k : ℝ) := by
  let A : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard k
  have hconst :
      ∀ s ∈ A,
        (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
            (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P) =
          ((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
            (∫ ω, X 0 ω ^ 2 ∂P) ^ k := by
    intro s hsA
    -- Proof comment: every pure pair profile contributes the same exact main-term factor.
    rw [pairProfileMultinomial_eq_factorial_div_pow hsA,
      pairProfileMoment_eq_secondMoment_pow (X := X) (P := P) hindep hident hsA]
  have hcard : A.card = n.choose k := by
    simpa [A] using (Finset.card_powersetCard k (Finset.univ : Finset (Fin n)))
  have hsum :
      Finset.sum A (fun s ↦
        (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
          (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P)) =
        (((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
          (∫ ω, X 0 ω ^ 2 ∂P) ^ k) * (n.choose k : ℝ) := by
    calc
      Finset.sum A (fun s ↦
          (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
            (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P))
          = Finset.sum A (fun _s ↦
              (((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
                (∫ ω, X 0 ω ^ 2 ∂P) ^ k)) := by
                refine Finset.sum_congr rfl ?_
                intro s hs
                exact hconst s hs
      _ = A.card *
            ((((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
              (∫ ω, X 0 ω ^ 2 ∂P) ^ k)) := by
              rw [Finset.sum_const, nsmul_eq_mul]
      _ = (((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) *
            (∫ ω, X 0 ω ^ 2 ∂P) ^ k) * (n.choose k : ℝ) := by
              rw [hcard]
              ring
  simpa [A] using hsum

/-- Helper for Exercise 15.4.6: in odd total degree, any profile without exponent `1` has support
cardinality at most `k - 1`. -/
lemma card_nonzero_profile_le_odd
    {k n : ℕ} (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i = 2 * k - 1)
    (h_no_one : ∀ i : Fin n, a i ≠ 1) :
    (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ k - 1 := by
  have hhalf :=
    two_mul_card_nonzero_profile_le (m := 2 * k - 1) a hsum h_no_one
  -- Proof comment: compare `2 * |support| ≤ 2k - 1` with the next even number `2k`.
  omega

/-- Helper for Exercise 15.4.6: in even total degree, a surviving profile with maximal possible
support has every nonzero exponent equal to `2`. -/
lemma nonzero_profile_eq_two_of_even_sum_support_eq
    {k n : ℕ} (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i = 2 * k)
    (h_no_one : ∀ i : Fin n, a i ≠ 1)
    (hsupp : (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = k) :
    ∀ i : Fin n, a i ≠ 0 → a i = 2 := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  have hs_sum : Finset.sum s a = 2 * k := by
    -- Proof comment: the profile sum lives entirely on the nonzero support.
    calc
      Finset.sum s a = ∑ i : Fin n, a i := by
        rw [show s = Finset.univ.filter fun i : Fin n ↦ a i ≠ 0 by rfl]
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro i hi
        by_cases hi0 : a i = 0
        · simp [hi0]
        · simp [hi0]
      _ = 2 * k := hsum
  intro i hi_nonzero
  have hi_mem : i ∈ s := by
    simp [s, hi_nonzero]
  have hrest_ge : 2 * (s.erase i).card ≤ Finset.sum (s.erase i) a := by
    -- Proof comment: all remaining support entries are still at least `2`.
    calc
      2 * (s.erase i).card = Finset.sum (s.erase i) (fun _ : Fin n ↦ 2) := by
        simp [two_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
      _ ≤ Finset.sum (s.erase i) a := by
        refine Finset.sum_le_sum ?_
        intro j hj
        have hj_mem : j ∈ s := Finset.mem_of_mem_erase hj
        have hj0 : a j ≠ 0 := by
          simpa [s] using (Finset.mem_filter.mp hj_mem).2
        have hj1 : a j ≠ 1 := h_no_one j
        omega
  have hs_erase : (s.erase i).card = k - 1 := by
    rw [Finset.card_erase_of_mem hi_mem, hsupp]
  have hs_decomp : Finset.sum s a = a i + Finset.sum (s.erase i) a := by
    simpa [add_comm] using (s.sum_erase_add a hi_mem).symm
  have hai_le_two : a i ≤ 2 := by
    have : a i + 2 * (k - 1) ≤ 2 * k := by
      calc
        a i + 2 * (k - 1) = a i + 2 * (s.erase i).card := by rw [hs_erase]
        _ ≤ a i + Finset.sum (s.erase i) a := Nat.add_le_add_left hrest_ge _
        _ = Finset.sum s a := hs_decomp.symm
        _ = 2 * k := hs_sum
    omega
  have hi1 : a i ≠ 1 := h_no_one i
  omega

/-- Helper for Exercise 15.4.6: in even total degree, every surviving profile that is not a pure
pair profile has support cardinality at most `k - 1`. -/
lemma card_nonzero_profile_le_even_of_not_all_two
    {k n : ℕ} (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i = 2 * k)
    (h_no_one : ∀ i : Fin n, a i ≠ 1)
    (h_not_all_two : ∃ i : Fin n, a i ≠ 0 ∧ a i ≠ 2) :
    (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ k - 1 := by
  have hhalf := two_mul_card_nonzero_profile_le (m := 2 * k) a hsum h_no_one
  have hsupp_le :
      (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ k := by
    omega
  by_cases hsupp :
      (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = k
  · obtain ⟨i, hi0, hi2⟩ := h_not_all_two
    have hall_two := nonzero_profile_eq_two_of_even_sum_support_eq a hsum h_no_one hsupp i hi0
    exact (hi2 hall_two).elim
  · omega

/-- Helper for Exercise 15.4.6: an even profile with no exponent `1` and maximal support is the
pure pair profile of its support. -/
lemma profile_eq_pairProfile_of_even_sum_support_eq
    {k n : ℕ} (a : Fin n → ℕ)
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (2 * k))
    (h_no_one : ∀ i : Fin n, a i ≠ 1)
    (hsupp : (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = k) :
    let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
    s ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ a = pairProfile s := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  change s ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ a = pairProfile s
  have hsum : ∑ i : Fin n, a i = 2 * k := (Finset.mem_piAntidiag.mp ha).1
  refine ⟨?_, ?_⟩
  · -- Proof comment: the support is by construction a `k`-subset of `Fin n`.
    simp [s, hsupp]
  · -- Proof comment: on the support every exponent is `2`, and off the support every exponent is
    -- `0`, so the profile is exactly the pure pair profile of its support.
    ext i
    by_cases hi : i ∈ s
    · have hi0 : a i ≠ 0 := by
        simpa [s] using (Finset.mem_filter.mp hi).2
      have htwo := nonzero_profile_eq_two_of_even_sum_support_eq a hsum h_no_one hsupp i hi0
      simp [pairProfile, hi, htwo]
    · have hi0 : a i = 0 := by
        by_contra hne
        exact hi (by simp [s, hne])
      simp [pairProfile, hi, hi0]

/-- Helper for Exercise 15.4.6: a `k`-subset of `Fin n` yields a maximal-support pure pair
profile in the even moment expansion, and its support is exactly that subset. -/
lemma pairProfile_mem_evenPairBlock
    {k n : ℕ} {s : Finset (Fin n)}
    (hs : s ∈ (Finset.univ : Finset (Fin n)).powersetCard k) :
    pairProfile s ∈
        ((Finset.piAntidiag (Finset.univ : Finset (Fin n)) (2 * k)).filter
          (fun a ↦ ¬ ∃ i : Fin n, a i = 1)).filter
          (fun a ↦ (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = k) ∧
      (Finset.univ.filter fun i : Fin n ↦ pairProfile s i ≠ 0) = s := by
  classical
  have hsupport :
      (Finset.univ.filter fun i : Fin n ↦ pairProfile s i ≠ 0) = s := by
    -- Proof comment: the pair profile is nonzero exactly on the chosen support `s`.
    ext i
    by_cases hi : i ∈ s
    · simp [pairProfile, hi]
    · simp [pairProfile, hi]
  have hsum_pair : ∑ i : Fin n, pairProfile s i = 2 * k := by
    -- Proof comment: the pair profile contributes `2` on `s` and `0` outside `s`.
    calc
      ∑ i : Fin n, pairProfile s i = ∑ i : Fin n, if i ∈ s then 2 else 0 := by
        rfl
      _ = Finset.sum s (fun _ : Fin n ↦ (2 : ℕ)) := by
            simpa using (Finset.sum_ite_mem (s := s) (f := fun _ : Fin n ↦ (2 : ℕ)))
      _ = 2 * k := by
            simpa [Nat.mul_comm, (Finset.mem_powersetCard.mp hs).2]
  refine ⟨?_, hsupport⟩
  refine Finset.mem_filter.mpr ⟨?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · refine Finset.mem_piAntidiag.mpr ⟨hsum_pair, ?_⟩
      intro i hi
      simp
    · -- Proof comment: a pure pair profile only takes the values `0` and `2`, never `1`.
      intro hOne
      rcases hOne with ⟨i, hi⟩
      by_cases hi_mem : i ∈ s
      · simp [pairProfile, hi_mem] at hi
      · simp [pairProfile, hi_mem] at hi
  · -- Proof comment: the support cardinality is exactly `k` because the support is `s`.
    simpa [hsupport] using (Finset.mem_powersetCard.mp hs).2

/-- Helper for Exercise 15.4.6: every even profile is either killed by an exponent `1`, is the
maximal-support pure pair profile of its support, or has support size at most `k - 1`. -/
lemma evenProfileTrichotomy
    {k n : ℕ} (a : Fin n → ℕ)
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) (2 * k)) :
    (∃ i : Fin n, a i = 1) ∨
      ((let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
        s ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ a = pairProfile s)) ∨
      (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ k - 1 := by
  classical
  by_cases hOne : ∃ i : Fin n, a i = 1
  · exact Or.inl hOne
  · have h_no_one : ∀ i : Fin n, a i ≠ 1 := by
      intro i hi
      exact hOne ⟨i, hi⟩
    by_cases hsupp : (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = k
    · -- Proof comment: the maximal-support non-singleton case is exactly the pure pair profile.
      exact Or.inr <| Or.inl <|
        profile_eq_pairProfile_of_even_sum_support_eq a ha h_no_one hsupp
    · have hsum : ∑ i : Fin n, a i = 2 * k := (Finset.mem_piAntidiag.mp ha).1
      have hhalf := two_mul_card_nonzero_profile_le a hsum h_no_one
      have hsupp_le :
          (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ k := by
        omega
      -- Proof comment: outside the maximal-support case, the even half-support bound forces one
      -- fewer active coordinate.
      exact Or.inr <| Or.inr <| by
        omega

/-- Helper for Exercise 15.4.6: `degreeMomentEnvelope m` is a finite constant that dominates the
absolute moments of the common law up to degree `m`. -/
def degreeMomentEnvelope (X : ℕ → Ω → ℝ) (P : Measure Ω) [IsProbabilityMeasure P]
    (m : ℕ) : ℝ :=
  Finset.sum (Finset.range (m + 1)) fun r ↦ 1 + ∫ ω, |X 0 ω| ^ r ∂P

/-- Helper for Exercise 15.4.6: the degree envelope is nonnegative. -/
lemma degreeMomentEnvelope_nonneg (m : ℕ) :
    0 ≤ degreeMomentEnvelope (X := X) (P := P) m := by
  -- Proof comment: each summand is `1` plus a nonnegative integral of a nonnegative function.
  refine Finset.sum_nonneg ?_
  intro r hr
  have hint :
      0 ≤ ∫ ω, |X 0 ω| ^ r ∂P := by
    refine integral_nonneg ?_
    intro ω
    positivity
  linarith

/-- Helper for Exercise 15.4.6: the degree envelope is at least `1`, so its powers are monotone
in the exponent. -/
lemma one_le_degreeMomentEnvelope (m : ℕ) :
    1 ≤ degreeMomentEnvelope (X := X) (P := P) m := by
  have hnonneg :
      ∀ r ∈ Finset.range (m + 1), 0 ≤ 1 + ∫ ω, |X 0 ω| ^ r ∂P := by
    intro r hr
    have hint :
        0 ≤ ∫ ω, |X 0 ω| ^ r ∂P := by
      refine integral_nonneg ?_
      intro ω
      positivity
    linarith
  have hzero :
      1 ≤ 1 + ∫ ω, |X 0 ω| ^ 0 ∂P := by
    have hint :
        0 ≤ ∫ ω, |X 0 ω| ^ 0 ∂P := by
      refine integral_nonneg ?_
      intro ω
      positivity
    linarith
  have hsingle :
      1 + ∫ ω, |X 0 ω| ^ 0 ∂P ≤ degreeMomentEnvelope (X := X) (P := P) m := by
    -- Proof comment: keep the zeroth-degree summand and use nonnegativity on the remaining ones.
    simpa [degreeMomentEnvelope] using
      (Finset.single_le_sum hnonneg (by simp : 0 ∈ Finset.range (m + 1)))
  exact le_trans hzero hsingle

/-- Helper for Exercise 15.4.6: a single coordinate moment of degree at most `m` is bounded by the
degree envelope. -/
lemma absCoordinateMoment_le_degreeEnvelope
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    {a m : ℕ} (ha : a ≤ m) (i : ℕ) :
    |∫ ω, X i ω ^ a ∂P| ≤ degreeMomentEnvelope (X := X) (P := P) m := by
  have hAbsIdent :
      IdentDistrib (fun ω ↦ |X i ω| ^ a) (fun ω ↦ |X 0 ω| ^ a) P P := by
    -- Proof comment: push identical distribution through the measurable map
    -- `x ↦ |x| ^ a` so every coordinate has the same absolute `a`th moment.
    simpa [Function.comp] using (hident i).comp (measurable_abs.pow_const a)
  have hAbsi_int : Integrable (fun ω ↦ |X i ω| ^ a) P :=
    (hAbsIdent.integrable_iff).2 (h_moments a)
  have hAbs0_nonneg : 0 ≤ ∫ ω, |X 0 ω| ^ a ∂P := by
    refine integral_nonneg ?_
    intro ω
    positivity
  have hterm_nonneg :
      ∀ r ∈ Finset.range (m + 1), 0 ≤ 1 + ∫ ω, |X 0 ω| ^ r ∂P := by
    intro r hr
    have hnonneg : 0 ≤ ∫ ω, |X 0 ω| ^ r ∂P := by
      refine integral_nonneg ?_
      intro ω
      positivity
    linarith
  have ha_mem : a ∈ Finset.range (m + 1) := by
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le ha)
  have hsummand_le :
      1 + ∫ ω, |X 0 ω| ^ a ∂P ≤ degreeMomentEnvelope (X := X) (P := P) m := by
    -- Proof comment: the degree-`a` absolute moment is one summand of the envelope.
    simpa [degreeMomentEnvelope] using
      (Finset.single_le_sum hterm_nonneg ha_mem)
  have hmoment_le :
      ∫ ω, |X 0 ω| ^ a ∂P ≤ degreeMomentEnvelope (X := X) (P := P) m := by
    linarith
  -- Proof comment: bound the mixed moment by the absolute moment, transport it to coordinate `0`,
  -- and then keep that moment inside the finite envelope.
  calc
    |∫ ω, X i ω ^ a ∂P| ≤ ∫ ω, |X i ω ^ a| ∂P := MeasureTheory.abs_integral_le_integral_abs
    _ = ∫ ω, |X i ω| ^ a ∂P := by
          congr 1
          ext ω
          simp [abs_pow]
    _ = ∫ ω, |X 0 ω| ^ a ∂P := by
          simpa using hAbsIdent.integral_eq
    _ ≤ degreeMomentEnvelope (X := X) (P := P) m := hmoment_le

/-- Helper for Exercise 15.4.6: the support of a tuple multiplicity profile has cardinal at most
the tuple length. -/
lemma card_nonzero_tupleMultiplicity_le {m n : ℕ} (u : Fin m → Fin n) :
    (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card ≤ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0
  have hs_le_sum : s.card ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := by
    -- Proof comment: every multiplicity on the support is at least `1`.
    calc
      s.card = Finset.sum s (fun _ : Fin n ↦ 1) := by simp
      _ ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi0 : tupleMultiplicity u i ≠ 0 := by
          simpa [s] using (Finset.mem_filter.mp hi).2
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
  have hs_sum : Finset.sum s (fun i ↦ tupleMultiplicity u i) = ∑ i : Fin n, tupleMultiplicity u i := by
    -- Proof comment: coordinates off the support contribute `0`, so the restricted sum is exact.
    rw [show s = Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0 by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi0 : tupleMultiplicity u i = 0
    · simp [hi0]
    · simp [hi0]
  calc
    (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card = s.card := by
      rfl
    _ ≤ Finset.sum s (fun i ↦ tupleMultiplicity u i) := hs_le_sum
    _ = ∑ i : Fin n, tupleMultiplicity u i := hs_sum
    _ = m := sum_tupleMultiplicity u

/-- Helper for Exercise 15.4.6: every tuple-word mixed moment of total degree `m` is bounded by
the `m`th power of the degree envelope. -/
lemma absTupleMoment_le_degreeEnvelope
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    {m n : ℕ} (u : Fin m → Fin n) :
    |∫ ω, ∏ j : Fin m, X (u j) ω ∂P| ≤ degreeMomentEnvelope (X := X) (P := P) m ^ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0
  have hfactor := tupleMoment_eq_prodIntegrals (X := X) (P := P) hindep hident u
  have hmult_le (i : Fin n) : tupleMultiplicity u i ≤ m := by
    calc
      tupleMultiplicity u i ≤ ∑ j : Fin n, tupleMultiplicity u j := by
        simpa using
          (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      _ = m := sum_tupleMultiplicity u
  have hsupport_prod :
      (∏ i : Fin n, |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|) =
        Finset.prod s (fun i ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|) := by
    -- Proof comment: coordinates with zero multiplicity contribute the factor `1`, so only the
    -- multiplicity support matters in the product of coordinate moments.
    calc
      ∏ i : Fin n, |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|
          = ∏ i : Fin n,
              if i ∈ s then |∫ ω, X i ω ^ tupleMultiplicity u i ∂P| else 1 := by
                refine Finset.prod_congr rfl ?_
                intro i hi
                by_cases hi_mem : i ∈ s
                · simp [hi_mem]
                · have hi0 : tupleMultiplicity u i = 0 := by
                    by_contra hne
                    exact hi_mem (by simp [s, hne])
                  simp [hi_mem, hi0]
      _ = Finset.prod s (fun i ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|) := by
            simpa using
              (Finset.prod_ite_mem
                (s := s) (f := fun i : Fin n ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|))
  have hcoord_bound :
      ∀ i ∈ s, |∫ ω, X i ω ^ tupleMultiplicity u i ∂P| ≤
        degreeMomentEnvelope (X := X) (P := P) m := by
    intro i hi
    exact absCoordinateMoment_le_degreeEnvelope
      (X := X) (P := P) hident h_moments (hmult_le i) i
  have hprod_le :
      Finset.prod s (fun i ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|) ≤
        degreeMomentEnvelope (X := X) (P := P) m ^ s.card := by
    let f : Fin n → ℝ := fun i ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|
    let E : ℝ := degreeMomentEnvelope (X := X) (P := P) m
    have henv_nonneg : 0 ≤ degreeMomentEnvelope (X := X) (P := P) m :=
      degreeMomentEnvelope_nonneg (X := X) (P := P) m
    -- Proof comment: bound the finite product by induction, using the same envelope bound on each
    -- surviving support factor.
    have hsubset_prod :
        ∀ t : Finset (Fin n), t ⊆ s → Finset.prod t f ≤ E ^ t.card := by
      intro t ht
      induction t using Finset.induction_on with
      | empty =>
          simp [f, E]
      | @insert a t ha ih =>
          have ht_sub : t ⊆ s := by
            intro i hi
            exact ht (by simp [hi, ha])
          have ha_mem : a ∈ s := ht (by simp [ha])
          have hfa_le : f a ≤ E := by
            simpa [f, E] using hcoord_bound a ha_mem
          have hprod_nonneg : 0 ≤ Finset.prod t f := by
            refine Finset.prod_nonneg ?_
            intro i hi
            exact abs_nonneg _
          have hpow_nonneg : 0 ≤ E ^ t.card := by
            exact pow_nonneg henv_nonneg _
          calc
            Finset.prod (insert a t) f = f a * Finset.prod t f := by
              simp [ha]
            _ ≤ E * E ^ t.card := by
                  exact mul_le_mul hfa_le (ih ht_sub) hprod_nonneg henv_nonneg
            _ = E ^ (t.card + 1) := by
                  rw [pow_succ']
            _ = E ^ (insert a t).card := by
                  simp [ha]
    simpa [f, E] using hsubset_prod s (by intro i hi; exact hi)
  have hs_card : s.card ≤ m := by
    simpa [s] using card_nonzero_tupleMultiplicity_le u
  have hpow_mono :
      degreeMomentEnvelope (X := X) (P := P) m ^ s.card ≤
        degreeMomentEnvelope (X := X) (P := P) m ^ m := by
    exact pow_le_pow_right₀ (one_le_degreeMomentEnvelope (X := X) (P := P) m) hs_card
  -- Proof comment: after reducing to the support product, the number of nontrivial factors is at
  -- most `m`, so the whole mixed moment is controlled by the `m`th power of the envelope.
  calc
    |∫ ω, ∏ j : Fin m, X (u j) ω ∂P|
        = Finset.prod s (fun i ↦ |∫ ω, X i ω ^ tupleMultiplicity u i ∂P|) := by
            rw [hfactor, Finset.abs_prod, hsupport_prod]
    _ ≤ degreeMomentEnvelope (X := X) (P := P) m ^ s.card := hprod_le
    _ ≤ degreeMomentEnvelope (X := X) (P := P) m ^ m := hpow_mono

/-- Helper for Exercise 15.4.6: in odd total degree, a tuple word without singleton
multiplicities has support cardinality at most `k - 1`. -/
lemma card_nonzero_tupleMultiplicity_le_odd
    {k n : ℕ} (u : Fin (2 * k - 1) → Fin n)
    (hk : 1 ≤ k)
    (h_no_one : ∀ i : Fin n, tupleMultiplicity u i ≠ 1) :
    (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card ≤ k - 1 := by
  have hhalf := two_mul_card_nonzero_tupleMultiplicity_le u h_no_one
  -- Proof comment: compare the half-support bound with the next even integer `2 * k`.
  omega

/-- Helper for Exercise 15.4.6: a fixed-degree monomial on `Fin n` is dominated by the sum of the
corresponding pure `m`th powers. -/
lemma monomialAbs_le_sumAbsPow_of_sum_eq
    {m n : ℕ} (hm : 0 < m) (a : Fin n → ℕ) (z : Fin n → ℝ)
    (hsum : ∑ i : Fin n, a i = m) :
    ∏ i : Fin n, |z i| ^ a i ≤ ∑ i : Fin n, |z i| ^ m := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast hm.ne'
  have hm_pos : (0 : ℝ) < m := by
    exact_mod_cast hm
  have hsum_cast : ∑ i : Fin n, (a i : ℝ) = m := by
    exact_mod_cast hsum
  have hweights_nonneg : ∀ i : Fin n, 0 ≤ (a i : ℝ) / m := by
    intro i
    exact div_nonneg (Nat.cast_nonneg _) (le_of_lt hm_pos)
  have hweights_sum : ∑ i : Fin n, (a i : ℝ) / m = 1 := by
    calc
      ∑ i : Fin n, (a i : ℝ) / m = (∑ i : Fin n, (a i : ℝ)) / m := by
        rw [Finset.sum_div]
      _ = (m : ℝ) / m := by rw [hsum_cast]
      _ = 1 := by field_simp [hm0]
  have hweights_le_one : ∀ i : Fin n, (a i : ℝ) / m ≤ 1 := by
    intro i
    have hi_le : a i ≤ m := by
      calc
        a i ≤ ∑ j : Fin n, a j := by
          simpa using
            (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
              (by simp : i ∈ (Finset.univ : Finset (Fin n))))
        _ = m := hsum
    have hi_cast : (a i : ℝ) ≤ m := by
      exact_mod_cast hi_le
    have hm_inv_nonneg : 0 ≤ (m : ℝ)⁻¹ := by
      positivity
    calc
      (a i : ℝ) / m = (a i : ℝ) * (m : ℝ)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ m * (m : ℝ)⁻¹ := by
            exact mul_le_mul_of_nonneg_right hi_cast hm_inv_nonneg
      _ = 1 := by
            field_simp [hm0]
  have hgeom :=
    Real.geom_mean_le_arith_mean_weighted
      (s := (Finset.univ : Finset (Fin n)))
      (w := fun i : Fin n ↦ (a i : ℝ) / m)
      (z := fun i : Fin n ↦ |z i| ^ m)
      (fun i _ ↦ hweights_nonneg i)
      hweights_sum
      (fun i _ ↦ by positivity)
  have hleft :
      ∏ i : Fin n, (|z i| ^ m) ^ ((a i : ℝ) / m) = ∏ i : Fin n, |z i| ^ a i := by
    refine Finset.prod_congr rfl ?_
    intro i hi
    calc
      (|z i| ^ m) ^ ((a i : ℝ) / m) = |z i| ^ ((m : ℝ) * ((a i : ℝ) / m)) := by
        rw [← Real.rpow_natCast_mul (abs_nonneg (z i)) m ((a i : ℝ) / m)]
      _ = |z i| ^ (a i : ℝ) := by
        congr 2
        field_simp [hm0]
      _ = |z i| ^ a i := by
        rw [Real.rpow_natCast]
  have hright :
      ∑ i : Fin n, ((a i : ℝ) / m) * |z i| ^ m ≤ ∑ i : Fin n, |z i| ^ m := by
    calc
      ∑ i : Fin n, ((a i : ℝ) / m) * |z i| ^ m
          ≤ ∑ i : Fin n, 1 * |z i| ^ m := by
              refine Finset.sum_le_sum ?_
              intro i hi
              exact mul_le_mul_of_nonneg_right (hweights_le_one i) (by positivity)
      _ = ∑ i : Fin n, |z i| ^ m := by simp
  -- Proof comment: apply weighted AM-GM with weights `a i / m`, then drop the weights on the
  -- arithmetic-mean side because each weight is at most `1`.
  calc
    ∏ i : Fin n, |z i| ^ a i = ∏ i : Fin n, (|z i| ^ m) ^ ((a i : ℝ) / m) := hleft.symm
    _ ≤ ∑ i : Fin n, ((a i : ℝ) / m) * |z i| ^ m := hgeom
    _ ≤ ∑ i : Fin n, |z i| ^ m := hright

/-- Helper for Exercise 15.4.6: a tuple-word product of positive length is integrable once the
common absolute moment of the same degree is integrable. -/
lemma integrable_tupleWordProduct_of_positive
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    {m n : ℕ} (hm : 0 < m) (u : Fin m → Fin n) :
    Integrable (fun ω ↦ ∏ j : Fin m, X (u j) ω) P := by
  have hcoord_int : ∀ i : Fin n, Integrable (fun ω ↦ |X i ω| ^ m) P := by
    intro i
    have hAbsIdent :
        IdentDistrib (fun ω ↦ |X i ω| ^ m) (fun ω ↦ |X 0 ω| ^ m) P P := by
      -- Proof comment: transport the common `m`th absolute moment to each coordinate by pushing
      -- identical distribution through `x ↦ |x| ^ m`.
      simpa [Function.comp] using (hident i).comp (measurable_abs.pow_const m)
    exact (hAbsIdent.integrable_iff).2 (h_moments m)
  have hsum_int : Integrable (fun ω ↦ ∑ i : Fin n, |X i ω| ^ m) P := by
    -- Proof comment: the dominating sum has finitely many summands, each with the common
    -- integrable `m`th absolute moment.
    exact MeasureTheory.integrable_finset_sum _ fun i _ ↦ hcoord_int i
  have hprod_meas :
      AEStronglyMeasurable (fun ω ↦ ∏ j : Fin m, X (u j) ω) P := by
    -- Proof comment: finite products of a.e.-strongly measurable coordinates are again
    -- a.e.-strongly measurable.
    simpa using
      (Finset.aestronglyMeasurable_fun_prod (s := (Finset.univ : Finset (Fin m))) fun j _ ↦
        ((hident (u j)).aemeasurable_fst.aestronglyMeasurable))
  refine Integrable.mono' hsum_int hprod_meas ?_
  filter_upwards with ω
  -- Proof comment: rewrite the tuple product by multiplicities and then apply the monomial
  -- domination lemma at total degree `m`.
  calc
    ‖∏ j : Fin m, X (u j) ω‖ = ∏ j : Fin m, |X (u j) ω| := by
      rw [Real.norm_eq_abs, Finset.abs_prod]
    _ = ∏ i : Fin n, |X i ω| ^ tupleMultiplicity u i := by
      simpa using prod_apply_eq_prod_pow_tupleMultiplicity u (fun i ↦ |X i ω|)
    _ ≤ ∑ i : Fin n, |X i ω| ^ m := by
      exact monomialAbs_le_sumAbsPow_of_sum_eq hm (tupleMultiplicity u) (fun i ↦ X i ω)
        (sum_tupleMultiplicity u)

-- Proof sketch: expand the odd power of the partial sum, group terms by mixed moments, use
-- independence and centering to discard the configurations with singleton indices, and count the
-- surviving terms to obtain an `n^(k-1)` bound.
/-- Odd moments of centered iid partial sums grow at most like `n^(k - 1)`. -/
theorem exists_odd_moment_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k - 1) ∂P| ≤
            d (2 * k - 1) * (n : ℝ) ^ (k - 1) := by
  classical
  let d : ℕ → ℝ := fun m ↦
    if hm : 0 < m then
      let C : ℕ := Classical.choose (smallSupportTupleCount_bound (m := m) (r := m / 2) hm)
      (C : ℝ) * degreeMomentEnvelope (X := X) (P := P) m ^ m
    else 0
  refine ⟨d, ?_⟩
  intro k n hk
  let m : ℕ := 2 * k - 1
  have hm : 0 < m := by
    dsimp [m]
    omega
  let E : ℝ := degreeMomentEnvelope (X := X) (P := P) m ^ m
  let p : (Fin m → Fin n) → Prop := fun u ↦
    (Finset.univ.filter fun i : Fin n ↦ tupleMultiplicity u i ≠ 0).card ≤ k - 1
  let C : ℕ := Classical.choose (smallSupportTupleCount_bound (m := m) (r := m / 2) hm)
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact pow_nonneg (degreeMomentEnvelope_nonneg (X := X) (P := P) m) m
  have hCbound_nat :
      (((Finset.univ : Finset (Fin m → Fin n)).filter p).card ≤ C * n ^ (k - 1)) := by
    have hchosen :=
      Classical.choose_spec (smallSupportTupleCount_bound (m := m) (r := m / 2) hm) n
    have hhalf : m / 2 = k - 1 := by
      dsimp [m]
      omega
    simpa [C, p, hhalf] using hchosen
  have hCbound :
      ((((Finset.univ : Finset (Fin m → Fin n)).filter p).card : ℕ) : ℝ) ≤
        (C : ℝ) * (n : ℝ) ^ (k - 1) := by
    exact_mod_cast hCbound_nat
  have hterm_bound (u : Fin m → Fin n) :
      |∫ ω, ∏ j : Fin m, X (u j) ω ∂P| ≤ if p u then E else 0 := by
    by_cases hu : p u
    · -- Proof comment: on the small-support region, the uniform degree-envelope bound closes the
      -- mixed moment directly.
      simpa [E, p, hu] using
        (absTupleMoment_le_degreeEnvelope
          (X := X) (P := P) hindep hident h_moments (u := u))
    · have hexists_one : ∃ i : Fin n, tupleMultiplicity u i = 1 := by
        by_contra hno
        have h_no_one : ∀ i : Fin n, tupleMultiplicity u i ≠ 1 := by
          intro i hi
          exact hno ⟨i, hi⟩
        have hsupp : p u := by
          dsimp [p]
          simpa [m] using
            (card_nonzero_tupleMultiplicity_le_odd (u := u) (n := n) hk h_no_one)
        exact hu hsupp
      rcases hexists_one with ⟨i, hi⟩
      have hzero :
          ∫ ω, ∏ j : Fin m, X (u j) ω ∂P = 0 := by
        -- Proof comment: a singleton multiplicity forces a centered first moment factor, so the
        -- whole mixed moment vanishes.
        exact tupleMoment_eq_zero_of_tupleMultiplicity_eq_one
          (X := X) (P := P) hindep hident h0 u hi
      simp [E, hu, hzero, hE_nonneg]
  have hintegrable :
      ∀ u ∈ (Finset.univ : Finset (Fin m → Fin n)),
        Integrable (fun ω ↦ ∏ j : Fin m, X (u j) ω) P := by
    intro u hu
    exact integrable_tupleWordProduct_of_positive
      (X := X) (P := P) hident h_moments hm u
  have hmain :
      |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P| ≤
        d m * (n : ℝ) ^ (k - 1) := by
    -- Proof comment: expand the odd power over tuple words, discard the singleton terms, and
    -- count the surviving small-support configurations.
    calc
      |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P|
          = |∑ u : Fin m → Fin n, ∫ ω, ∏ j : Fin m, X (u j) ω ∂P| := by
              congr 1
              calc
                ∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P
                    = ∫ ω, ∑ u : Fin m → Fin n, ∏ j : Fin m, X (u j) ω ∂P := by
                        refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
                        simpa [partialSum_eq_sum_univ_fin (X := X) (n := n) (ω := ω)] using
                          (partialSumPow_eq_sum_tupleWords (X := X) (m := m) (n := n) (ω := ω))
                _ = ∑ u : Fin m → Fin n, ∫ ω, ∏ j : Fin m, X (u j) ω ∂P := by
                      simpa using
                        (MeasureTheory.integral_finset_sum
                          (μ := P)
                          (s := (Finset.univ : Finset (Fin m → Fin n)))
                          (f := fun u ω ↦ ∏ j : Fin m, X (u j) ω)
                          hintegrable)
      _ ≤ ∑ u : Fin m → Fin n, |∫ ω, ∏ j : Fin m, X (u j) ω ∂P| := by
            simpa using
              (Finset.abs_sum_le_sum_abs
                (s := (Finset.univ : Finset (Fin m → Fin n)))
                (f := fun u ↦ ∫ ω, ∏ j : Fin m, X (u j) ω ∂P))
      _ ≤ ∑ u : Fin m → Fin n, if p u then E else 0 := by
            refine Finset.sum_le_sum ?_
            intro u hu
            exact hterm_bound u
      _ = ((((Finset.univ : Finset (Fin m → Fin n)).filter p).card : ℕ) : ℝ) * E := by
            rw [← Finset.sum_filter]
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((C : ℝ) * (n : ℝ) ^ (k - 1)) * E := by
            gcongr
      _ = d m * (n : ℝ) ^ (k - 1) := by
            rw [show d m = (C : ℝ) * E by simp [d, C, E, hm]]
            ring
  simpa [m] using hmain

/-- Helper for Exercise 15.4.6: the support of a profile on `Fin n` has cardinality at most its
total degree. -/
lemma card_nonzero_profile_le
    {m n : ℕ} (a : Fin n → ℕ)
    (hsum : ∑ i : Fin n, a i = m) :
    (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  have hs_le_sum : s.card ≤ Finset.sum s a := by
    -- Proof comment: every profile coordinate on the support is at least `1`.
    calc
      s.card = Finset.sum s (fun _ : Fin n ↦ 1) := by simp
      _ ≤ Finset.sum s a := by
        refine Finset.sum_le_sum ?_
        intro i hi
        have hi0 : a i ≠ 0 := by
          simpa [s] using (Finset.mem_filter.mp hi).2
        exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hi0)
  have hs_sum : Finset.sum s a = ∑ i : Fin n, a i := by
    -- Proof comment: outside the support all profile entries vanish, so the restriction is exact.
    rw [show s = Finset.univ.filter fun i : Fin n ↦ a i ≠ 0 by rfl]
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro i hi
    by_cases hi0 : a i = 0
    · simp [hi0]
    · simp [hi0]
  calc
    (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card = s.card := by
      rfl
    _ ≤ Finset.sum s a := hs_le_sum
    _ = ∑ i : Fin n, a i := hs_sum
    _ = m := hsum

/-- Helper for Exercise 15.4.6: a profile-indexed product of positive total degree is integrable
once the common absolute moment of the same degree is integrable. -/
lemma integrable_profileProduct_of_positive
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    {m n : ℕ} (hm : 0 < m) (a : Fin n → ℕ)
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m) :
    Integrable (fun ω ↦ ∏ i : Fin n, X i ω ^ a i) P := by
  have hsum : ∑ i : Fin n, a i = m := (Finset.mem_piAntidiag.mp ha).1
  have hcoord_int : ∀ i : Fin n, Integrable (fun ω ↦ |X i ω| ^ m) P := by
    intro i
    have hAbsIdent :
        IdentDistrib (fun ω ↦ |X i ω| ^ m) (fun ω ↦ |X 0 ω| ^ m) P P := by
      -- Proof comment: the common absolute `m`th moment transfers to every coordinate.
      simpa [Function.comp] using (hident i).comp (measurable_abs.pow_const m)
    exact (hAbsIdent.integrable_iff).2 (h_moments m)
  have hsum_int : Integrable (fun ω ↦ ∑ i : Fin n, |X i ω| ^ m) P := by
    -- Proof comment: finite sums preserve integrability once each coordinate term is integrable.
    exact MeasureTheory.integrable_finset_sum _ fun i _ ↦ hcoord_int i
  have hprod_meas :
      AEStronglyMeasurable (fun ω ↦ ∏ i : Fin n, X i ω ^ a i) P := by
    -- Proof comment: each powered coordinate is a.e.-strongly measurable, so their finite
    -- product is as well.
    simpa using
      (Finset.aestronglyMeasurable_fun_prod (s := (Finset.univ : Finset (Fin n))) fun i _ ↦
        (((hident i).aemeasurable_fst.pow_const (a i)).aestronglyMeasurable))
  refine Integrable.mono' hsum_int hprod_meas ?_
  filter_upwards with ω
  -- Proof comment: after taking absolute values, the profile monomial is controlled by the same
  -- degree-`m` power sum as in the tuple-word case.
  calc
    ‖∏ i : Fin n, X i ω ^ a i‖ = ∏ i : Fin n, |X i ω| ^ a i := by
      rw [Real.norm_eq_abs, Finset.abs_prod]
      refine Finset.prod_congr rfl ?_
      intro i hi
      rw [abs_pow]
    _ ≤ ∑ i : Fin n, |X i ω| ^ m := by
      exact monomialAbs_le_sumAbsPow_of_sum_eq hm a (fun i ↦ X i ω) hsum

/-- Helper for Exercise 15.4.6: every profile-indexed mixed moment of total degree `m` is
bounded by the `m`th power of the degree envelope. -/
lemma absProfileMoment_le_degreeEnvelope
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    {m n : ℕ} (a : Fin n → ℕ)
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m) :
    |∫ ω, ∏ i : Fin n, X i ω ^ a i ∂P| ≤ degreeMomentEnvelope (X := X) (P := P) m ^ m := by
  classical
  let s : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  have hsum : ∑ i : Fin n, a i = m := (Finset.mem_piAntidiag.mp ha).1
  have hfactor := profileMoment_eq_prodCoordinateMoments (X := X) (P := P) hindep hident a
  have hmult_le (i : Fin n) : a i ≤ m := by
    calc
      a i ≤ ∑ j : Fin n, a j := by
        simpa using
          (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
            (by simp : i ∈ (Finset.univ : Finset (Fin n))))
      _ = m := hsum
  have hsupport_prod :
      (∏ i : Fin n, |∫ ω, X i ω ^ a i ∂P|) =
        Finset.prod s (fun i ↦ |∫ ω, X i ω ^ a i ∂P|) := by
    -- Proof comment: only the nonzero support contributes, since coordinates with exponent `0`
    -- contribute the trivial factor `1`.
    calc
      ∏ i : Fin n, |∫ ω, X i ω ^ a i ∂P|
          = ∏ i : Fin n, if i ∈ s then |∫ ω, X i ω ^ a i ∂P| else 1 := by
              refine Finset.prod_congr rfl ?_
              intro i hi
              by_cases hi_mem : i ∈ s
              · simp [hi_mem]
              · have hi0 : a i = 0 := by
                  by_contra hne
                  exact hi_mem (by simp [s, hne])
                simp [hi_mem, hi0]
      _ = Finset.prod s (fun i ↦ |∫ ω, X i ω ^ a i ∂P|) := by
            simpa using
              (Finset.prod_ite_mem (s := s) (f := fun i : Fin n ↦ |∫ ω, X i ω ^ a i ∂P|))
  have hcoord_bound :
      ∀ i ∈ s, |∫ ω, X i ω ^ a i ∂P| ≤ degreeMomentEnvelope (X := X) (P := P) m := by
    intro i hi
    exact absCoordinateMoment_le_degreeEnvelope
      (X := X) (P := P) hident h_moments (hmult_le i) i
  have hprod_le :
      Finset.prod s (fun i ↦ |∫ ω, X i ω ^ a i ∂P|) ≤
        degreeMomentEnvelope (X := X) (P := P) m ^ s.card := by
    let f : Fin n → ℝ := fun i ↦ |∫ ω, X i ω ^ a i ∂P|
    let E : ℝ := degreeMomentEnvelope (X := X) (P := P) m
    have henv_nonneg : 0 ≤ degreeMomentEnvelope (X := X) (P := P) m :=
      degreeMomentEnvelope_nonneg (X := X) (P := P) m
    -- Proof comment: bound the support product by induction, replacing each factor with the same
    -- degree envelope bound.
    have hsubset_prod :
        ∀ t : Finset (Fin n), t ⊆ s → Finset.prod t f ≤ E ^ t.card := by
      intro t ht
      induction t using Finset.induction_on with
      | empty =>
          simp [f, E]
      | @insert b t hb ih =>
          have ht_sub : t ⊆ s := by
            intro i hi
            exact ht (by simp [hi, hb])
          have hb_mem : b ∈ s := ht (by simp [hb])
          have hfb_le : f b ≤ E := by
            simpa [f, E] using hcoord_bound b hb_mem
          have hprod_nonneg : 0 ≤ Finset.prod t f := by
            refine Finset.prod_nonneg ?_
            intro i hi
            exact abs_nonneg _
          calc
            Finset.prod (insert b t) f = f b * Finset.prod t f := by
              simp [hb]
            _ ≤ E * E ^ t.card := by
                  exact mul_le_mul hfb_le (ih ht_sub) hprod_nonneg henv_nonneg
            _ = E ^ (t.card + 1) := by rw [pow_succ']
            _ = E ^ (insert b t).card := by simp [hb]
    simpa [f, E] using hsubset_prod s (by intro i hi; exact hi)
  have hs_card : s.card ≤ m := by
    simpa [s] using card_nonzero_profile_le a hsum
  have hpow_mono :
      degreeMomentEnvelope (X := X) (P := P) m ^ s.card ≤
        degreeMomentEnvelope (X := X) (P := P) m ^ m := by
    exact pow_le_pow_right₀ (one_le_degreeMomentEnvelope (X := X) (P := P) m) hs_card
  -- Proof comment: factor the mixed moment into one-dimensional moments, throw away the trivial
  -- zero-exponent factors, and bound each remaining coordinate moment by the common envelope.
  calc
    |∫ ω, ∏ i : Fin n, X i ω ^ a i ∂P|
        = Finset.prod s (fun i ↦ |∫ ω, X i ω ^ a i ∂P|) := by
            rw [hfactor, Finset.abs_prod, hsupport_prod]
    _ ≤ degreeMomentEnvelope (X := X) (P := P) m ^ s.card := hprod_le
    _ ≤ degreeMomentEnvelope (X := X) (P := P) m ^ m := hpow_mono

/-- Helper for Exercise 15.4.6: the number of degree-`m` profiles on `Fin n` with support of size
at most `r` is bounded by a fixed constant times `n ^ r`. -/
lemma smallSupportPiAntidiag_count_bound {m r : ℕ} (hm : 0 < m) :
    ∃ C : ℕ,
      ∀ n,
        (((Finset.piAntidiag (Finset.univ : Finset (Fin n)) m).filter
            fun a =>
              (Finset.univ.filter fun i : Fin n ↦ a i ≠ 0).card ≤ r).card ≤
          C * n ^ r) := by
  classical
  -- Route correction: count profiles by first choosing their support and then restricting the
  -- profile to that support as a function into `Fin (m + 1)`.
  let C : ℕ := ∑ t ∈ Finset.Icc 1 r, (m + 1) ^ t
  refine ⟨C, ?_⟩
  intro n
  cases n with
  | zero =>
      have hcard0 :
          (((Finset.piAntidiag (Finset.univ : Finset (Fin 0)) m).filter
              fun a =>
                (Finset.univ.filter fun i : Fin 0 ↦ a i ≠ 0).card ≤ r).card) = 0 := by
        simp [hm.ne']
      rw [hcard0]
      exact Nat.zero_le _
  | succ n =>
      let A : Finset (Fin (n + 1) → ℕ) :=
        (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) m).filter
          fun a =>
            (Finset.univ.filter fun i : Fin (n + 1) ↦ a i ≠ 0).card ≤ r
      let block (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1) → ℕ) :=
        (Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) m).filter
          fun a ↦ ∀ i : Fin (n + 1), a i ≠ 0 → i ∈ s
      let B : Finset (Fin (n + 1) → ℕ) :=
        (Finset.Icc 1 r).biUnion fun t =>
          (((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s => block s)
      have hsub : A ⊆ B := by
        intro a ha
        let s : Finset (Fin (n + 1)) := Finset.univ.filter fun i : Fin (n + 1) ↦ a i ≠ 0
        have ha_pi : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (n + 1))) m :=
          (Finset.mem_filter.mp ha).1
        have hs_le_r : s.card ≤ r := by
          simpa [A, s] using (Finset.mem_filter.mp ha).2
        have hs_nonempty : s.Nonempty := by
          by_contra hs_empty
          have hs_zero : ∀ i : Fin (n + 1), a i = 0 := by
            intro i
            by_contra hi
            exact hs_empty ⟨i, by simp [s, hi]⟩
          have hsum : ∑ i : Fin (n + 1), a i = m := (Finset.mem_piAntidiag.mp ha_pi).1
          have hm_zero : m = 0 := by
            calc
              m = ∑ i : Fin (n + 1), a i := hsum.symm
              _ = 0 := by simp [hs_zero]
          exact hm.ne' hm_zero
        have hs_mem_Icc : s.card ∈ Finset.Icc 1 r := by
          rw [Finset.mem_Icc]
          exact ⟨Finset.one_le_card.mpr hs_nonempty, hs_le_r⟩
        have hs_mem_powerset :
            s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard s.card := by
          exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ s, rfl⟩
        have ha_block : a ∈ block s := by
          refine Finset.mem_filter.mpr ⟨ha_pi, ?_⟩
          intro i hi
          simp [s, hi]
        exact Finset.mem_biUnion.2 ⟨s.card, hs_mem_Icc, Finset.mem_biUnion.2 ⟨s, hs_mem_powerset, ha_block⟩⟩
      have hblock_card :
          ∀ t ∈ Finset.Icc 1 r,
            ∀ s ∈ (Finset.univ : Finset (Fin (n + 1))).powersetCard t,
              (block s).card ≤ (m + 1) ^ t := by
        intro t ht s hs
        let F : (Fin (n + 1) → ℕ) → s → Fin (m + 1) := fun a i ↦
          ⟨min (a i.1) m, Nat.lt_succ_of_le (Nat.min_le_right _ _)⟩
        have hle_m :
            ∀ a ∈ block s, ∀ i : s, a i.1 ≤ m := by
          intro a ha i
          have hsum : ∑ j : Fin (n + 1), a j = m := (Finset.mem_piAntidiag.mp ((Finset.mem_filter.mp ha).1)).1
          calc
            a i.1 ≤ ∑ j : Fin (n + 1), a j := by
              simpa using
                (Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
                  (by simp : i.1 ∈ (Finset.univ : Finset (Fin (n + 1)))))
            _ = m := hsum
        have hF_maps : Set.MapsTo F (block s) (Finset.univ : Finset (s → Fin (m + 1))) := by
          intro a ha
          simp [F]
        have hF_inj : Set.InjOn F (block s) := by
          intro a ha b hb hab
          ext i
          by_cases hi : i ∈ s
          · have hai_le : a i ≤ m := hle_m a ha ⟨i, hi⟩
            have hbi_le : b i ≤ m := hle_m b hb ⟨i, hi⟩
            have hval :
                min (a i) m = min (b i) m := by
              exact congrArg Fin.val (congr_fun hab ⟨i, hi⟩)
            simpa [F, Nat.min_eq_left hai_le, Nat.min_eq_left hbi_le] using hval
          · have ha_support : ∀ j : Fin (n + 1), a j ≠ 0 → j ∈ s := (Finset.mem_filter.mp ha).2
            have hb_support : ∀ j : Fin (n + 1), b j ≠ 0 → j ∈ s := (Finset.mem_filter.mp hb).2
            have hai0 : a i = 0 := by
              by_contra hai
              exact hi (ha_support i hai)
            have hbi0 : b i = 0 := by
              by_contra hbi
              exact hi (hb_support i hbi)
            simp [hai0, hbi0]
        calc
          (block s).card ≤ (Finset.univ : Finset (s → Fin (m + 1))).card :=
            Finset.card_le_card_of_injOn F hF_maps hF_inj
          _ = (m + 1) ^ s.card := by simp
          _ = (m + 1) ^ t := by rw [(Finset.mem_powersetCard.mp hs).2]
      have hinner :
          ∀ t ∈ Finset.Icc 1 r,
            ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                block s).card) ≤
              ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * (m + 1) ^ t := by
        intro t ht
        refine Finset.card_biUnion_le_card_mul
          ((Finset.univ : Finset (Fin (n + 1))).powersetCard t)
          (fun s ↦ block s)
          ((m + 1) ^ t) ?_
        intro s hs
        exact hblock_card t ht s hs
      have hsum_le :
          B.card ≤ ∑ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * (m + 1) ^ t := by
        calc
          B.card ≤ ∑ t ∈ Finset.Icc 1 r,
              ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                  block s).card) := by
                simpa [B] using (Finset.card_biUnion_le :
                  ((Finset.Icc 1 r).biUnion fun t =>
                    (((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                      block s)).card ≤
                    ∑ t ∈ Finset.Icc 1 r,
                      ((((Finset.univ : Finset (Fin (n + 1))).powersetCard t).biUnion fun s =>
                          block s).card))
          _ ≤ ∑ t ∈ Finset.Icc 1 r,
              ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * (m + 1) ^ t := by
                refine Finset.sum_le_sum ?_
                intro t ht
                exact hinner t ht
      have hterm :
          ∀ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * (m + 1) ^ t ≤
              (m + 1) ^ t * (n + 1) ^ r := by
        intro t ht
        have ht_le_r : t ≤ r := (Finset.mem_Icc.mp ht).2
        have hchoose :
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card ≤ (n + 1) ^ t := by
          rw [Finset.card_powersetCard]
          simpa using (Nat.choose_le_pow (n + 1) t)
        have hpow : (n + 1) ^ t ≤ (n + 1) ^ r := by
          exact Nat.pow_le_pow_right (Nat.succ_pos _) ht_le_r
        simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
          Nat.mul_le_mul_right ((m + 1) ^ t) (hchoose.trans hpow)
      -- Proof comment: cover profiles by their exact support, inject each support block into
      -- functions valued in `Fin (m + 1)`, and then count support choices by binomial bounds.
      calc
        A.card ≤ B.card := Finset.card_le_card hsub
        _ ≤ ∑ t ∈ Finset.Icc 1 r,
            ((Finset.univ : Finset (Fin (n + 1))).powersetCard t).card * (m + 1) ^ t := hsum_le
        _ ≤ ∑ t ∈ Finset.Icc 1 r, (m + 1) ^ t * (n + 1) ^ r := by
              refine Finset.sum_le_sum ?_
              intro t ht
              exact hterm t ht
        _ = C * (n + 1) ^ r := by
              simp [C, Finset.sum_mul]

/-- Helper for Exercise 15.4.6: a multinomial coefficient of total degree `m` is at most `m!`. -/
lemma multinomial_le_factorial_of_piAntidiag
    {m n : ℕ} {a : Fin n → ℕ}
    (ha : a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin n)) m) :
    Nat.multinomial (Finset.univ : Finset (Fin n)) a ≤ Nat.factorial m := by
  have hsum : ∑ i : Fin n, a i = m := (Finset.mem_piAntidiag.mp ha).1
  have hprod_pos : 0 < ∏ i : Fin n, Nat.factorial (a i) := by
    -- Proof comment: every factorial factor is positive, so the whole denominator product is
    -- positive as well.
    refine Finset.prod_pos ?_
    intro i hi
    exact Nat.factorial_pos _
  -- Proof comment: the multinomial identity writes `m!` as the multinomial coefficient times a
  -- positive product of factorials, so dropping that extra factor only decreases the value.
  calc
    Nat.multinomial (Finset.univ : Finset (Fin n)) a
        ≤ Nat.multinomial (Finset.univ : Finset (Fin n)) a *
            ∏ i : Fin n, Nat.factorial (a i) := by
              exact Nat.le_mul_of_pos_right _ hprod_pos
    _ = Nat.factorial m := by
          simpa [hsum, Nat.mul_comm] using
            (Nat.multinomial_spec (s := (Finset.univ : Finset (Fin n))) (f := a))

/-- Helper for Exercise 15.4.6: for fixed `k + 1`, the gap between `n^(k + 1)` and the
descending factorial `n.descFactorial (k + 1)` is `O(n^k)`. -/
lemma pow_sub_descFactorial_succ_bound :
    ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      (n : ℝ) ^ (k + 1) - n.descFactorial (k + 1) ≤ C * (n : ℝ) ^ k := by
  intro k
  induction k with
  | zero =>
      refine ⟨0, le_rfl, ?_⟩
      intro n
      -- Proof comment: in degree `1`, the descending factorial is exactly `n`, so the gap
      -- vanishes.
      simp
  | succ k ih =>
      rcases ih with ⟨C, hC_nonneg, hC⟩
      refine ⟨C + (k + 1), add_nonneg hC_nonneg (by positivity), ?_⟩
      intro n
      by_cases hn : n ≤ k + 1
      · have hdesc_zero : n.descFactorial (k + 2) = 0 := by
          exact Nat.descFactorial_eq_zero_iff_lt.mpr (lt_of_le_of_lt hn (Nat.lt_succ_self _))
        -- Proof comment: below the truncation threshold the descending factorial vanishes, so the
        -- remaining power is controlled by the crude bound `n ≤ k + 1`.
        calc
          (n : ℝ) ^ (k + 2) - n.descFactorial (k + 2) = (n : ℝ) ^ (k + 2) := by
            rw [hdesc_zero, Nat.cast_zero, sub_zero]
          _ = (n : ℝ) * (n : ℝ) ^ (k + 1) := by rw [pow_succ']
          _ ≤ (k + 1 : ℝ) * (n : ℝ) ^ (k + 1) := by
                gcongr
                exact_mod_cast hn
          _ ≤ (C + (k + 1)) * (n : ℝ) ^ (k + 1) := by
                have hpow_nonneg : 0 ≤ (n : ℝ) ^ (k + 1) := by positivity
                nlinarith
      · have hnk : k + 1 ≤ n := le_of_lt (lt_of_not_ge hn)
        have hdesc_le : (n.descFactorial (k + 1) : ℝ) ≤ (n : ℝ) ^ (k + 1) := by
          exact_mod_cast Nat.descFactorial_le_pow n (k + 1)
        -- Proof comment: above the truncation threshold, factor off the last descending term and
        -- reuse the induction hypothesis on the remaining degree.
        calc
          (n : ℝ) ^ (k + 2) - n.descFactorial (k + 2)
              = (n : ℝ) * ((n : ℝ) ^ (k + 1) - n.descFactorial (k + 1)) +
                  (k + 1 : ℝ) * n.descFactorial (k + 1) := by
                    rw [Nat.descFactorial_succ, Nat.cast_mul, Nat.cast_sub hnk, pow_succ',
                      Nat.cast_add, Nat.cast_one]
                    ring
          _ ≤ (n : ℝ) * (C * (n : ℝ) ^ k) + (k + 1 : ℝ) * (n : ℝ) ^ (k + 1) := by
                have hn_nonneg : 0 ≤ (n : ℝ) := by positivity
                have hk_nonneg : 0 ≤ (k + 1 : ℝ) := by positivity
                have hfirst :
                    (n : ℝ) * ((n : ℝ) ^ (k + 1) - n.descFactorial (k + 1)) ≤
                      (n : ℝ) * (C * (n : ℝ) ^ k) := by
                  exact mul_le_mul_of_nonneg_left (hC n) hn_nonneg
                have hsecond :
                    (k + 1 : ℝ) * n.descFactorial (k + 1) ≤
                      (k + 1 : ℝ) * (n : ℝ) ^ (k + 1) := by
                  exact mul_le_mul_of_nonneg_left hdesc_le hk_nonneg
                nlinarith
          _ = (C + (k + 1)) * (n : ℝ) ^ (k + 1) := by
                ring_nf

/-- Helper for Exercise 15.4.6: `n.choose k` differs from `n^k / k!` by `O(n^(k - 1))`. -/
lemma choose_sub_pow_div_factorial_bound {k : ℕ} (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      |(n.choose k : ℝ) - (n : ℝ) ^ k / (Nat.factorial k : ℝ)| ≤
        C * (n : ℝ) ^ (k - 1) := by
  rcases pow_sub_descFactorial_succ_bound (k - 1) with ⟨C, hC_nonneg, hC⟩
  refine ⟨C / (Nat.factorial k : ℝ), div_nonneg hC_nonneg (by positivity), ?_⟩
  intro n
  have hfac_pos : 0 < (Nat.factorial k : ℝ) := by positivity
  have hfac_nonneg : 0 ≤ (Nat.factorial k : ℝ) := hfac_pos.le
  have hchoose :
      (n.choose k : ℝ) = (n.descFactorial k : ℝ) / (Nat.factorial k : ℝ) := by
    rw [Nat.choose_eq_descFactorial_div_factorial,
      Nat.cast_div (Nat.factorial_dvd_descFactorial n k) (by exact_mod_cast Nat.factorial_ne_zero k)]
  have hdesc_le : (n.descFactorial k : ℝ) ≤ (n : ℝ) ^ k := by
    exact_mod_cast Nat.descFactorial_le_pow n k
  have hgap :
      (n : ℝ) ^ k - n.descFactorial k ≤ C * (n : ℝ) ^ (k - 1) := by
    have hk_eq : (k - 1) + 1 = k := by omega
    simpa [hk_eq] using hC n
  have hnonpos :
      ((n.descFactorial k : ℝ) - (n : ℝ) ^ k) / (Nat.factorial k : ℝ) ≤ 0 := by
    exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hdesc_le) hfac_nonneg
  -- Proof comment: rewrite `choose` through the descending factorial, note that the difference
  -- has a fixed sign, and divide the previously established gap estimate by `k!`.
  calc
    |(n.choose k : ℝ) - (n : ℝ) ^ k / (Nat.factorial k : ℝ)|
        = |((n.descFactorial k : ℝ) - (n : ℝ) ^ k) / (Nat.factorial k : ℝ)| := by
            rw [hchoose]
            ring_nf
    _ = ((n : ℝ) ^ k - n.descFactorial k) / (Nat.factorial k : ℝ) := by
          rw [abs_of_nonpos hnonpos]
          ring
    _ ≤ (C * (n : ℝ) ^ (k - 1)) / (Nat.factorial k : ℝ) := by
          exact div_le_div_of_nonneg_right hgap hfac_nonneg
    _ = (C / (Nat.factorial k : ℝ)) * (n : ℝ) ^ (k - 1) := by
          field_simp [hfac_pos.ne']

-- Proof sketch: expand the even power of the partial sum, isolate the leading contribution from
-- pairings of distinct squared factors, identify its combinatorial coefficient
-- `(2k)! / (2^k k!)`, and bound all remaining index patterns by `n^(k-1)`.
/-- Exercise 15.4.6: even moments of centered iid partial sums have the Gaussian leading term up
to an `n^(k - 1)` error. -/
theorem exists_even_moment_expansion_bounds_of_iid_centered
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P) :
    ∃ d : ℕ → ℝ,
      ∀ k n : ℕ,
        1 ≤ k →
          |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ (2 * k) ∂P -
              (((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
                (∫ ω, X 0 ω ^ 2 ∂P) ^ k * (n : ℝ) ^ k)| ≤
            d (2 * k) * (n : ℝ) ^ (k - 1) := by
  classical
  let D : ℕ → ℝ := fun k ↦
    if hk : 1 ≤ k then
      let hm : 0 < 2 * k := by omega
      let Csmall : ℕ :=
        Classical.choose (smallSupportPiAntidiag_count_bound (m := 2 * k) (r := k - 1) hm)
      let Cchoose : ℝ := Classical.choose (choose_sub_pow_div_factorial_bound (k := k) hk)
      let E : ℝ :=
        (Nat.factorial (2 * k) : ℝ) *
          degreeMomentEnvelope (X := X) (P := P) (2 * k) ^ (2 * k)
      let Acoeff : ℝ :=
        ((Nat.factorial (2 * k) : ℝ) / ((2 : ℝ) ^ k)) * (∫ ω, X 0 ω ^ 2 ∂P) ^ k
      ((Csmall : ℝ) * E) + Acoeff * Cchoose
    else 0
  let d : ℕ → ℝ := fun m ↦ if Even m then D (m / 2) else 0
  refine ⟨d, ?_⟩
  intro k n hk
  let m : ℕ := 2 * k
  let A : Finset (Fin n → ℕ) := Finset.piAntidiag (Finset.univ : Finset (Fin n)) m
  let supp : (Fin n → ℕ) → Finset (Fin n) := fun a ↦ Finset.univ.filter fun i : Fin n ↦ a i ≠ 0
  let noOne : (Fin n → ℕ) → Prop := fun a ↦ ¬ ∃ i : Fin n, a i = 1
  let pairBlock : Finset (Fin n → ℕ) :=
    (A.filter noOne).filter fun a ↦ (supp a).card = k
  let remainderBlock : Finset (Fin n → ℕ) :=
    (A.filter noOne).filter fun a ↦ (supp a).card ≠ k
  let smallBlock : Finset (Fin n → ℕ) :=
    A.filter fun a ↦ (supp a).card ≤ k - 1
  let summand : (Fin n → ℕ) → ℝ := fun a ↦
    (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
      (∫ ω, ∏ i : Fin n, X i ω ^ a i ∂P)
  let Csmall : ℕ :=
    Classical.choose (smallSupportPiAntidiag_count_bound (m := m) (r := k - 1) (by
      dsimp [m]
      omega))
  let Cchoose : ℝ := Classical.choose (choose_sub_pow_div_factorial_bound (k := k) hk)
  let E : ℝ :=
    (Nat.factorial m : ℝ) * degreeMomentEnvelope (X := X) (P := P) m ^ m
  let Acoeff : ℝ :=
    ((Nat.factorial m : ℝ) / ((2 : ℝ) ^ k)) * (∫ ω, X 0 ω ^ 2 ∂P) ^ k
  let targetTerm : ℝ :=
    (((Nat.factorial m : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) *
      (∫ ω, X 0 ω ^ 2 ∂P) ^ k * (n : ℝ) ^ k)
  have hm : 0 < m := by
    dsimp [m]
    omega
  have hDk : D k = ((Csmall : ℝ) * E) + Acoeff * Cchoose := by
    simp [D, hk, Csmall, Cchoose, E, Acoeff, m]
  have hd_eval : d (2 * k) = ((Csmall : ℝ) * E) + Acoeff * Cchoose := by
    have hEven : Even (2 * k) := by
      refine ⟨k, ?_⟩
      omega
    have hdiv : (2 * k) / 2 = k := by
      omega
    simp [d, hEven, hdiv, hDk]
  have hE_nonneg : 0 ≤ E := by
    dsimp [E]
    exact mul_nonneg (by positivity)
      (pow_nonneg (degreeMomentEnvelope_nonneg (X := X) (P := P) m) _)
  have hCchoose_nonneg : 0 ≤ Cchoose := by
    exact (Classical.choose_spec (choose_sub_pow_div_factorial_bound (k := k) hk)).1
  have hchooseBound :
      ∀ n : ℕ,
        |(n.choose k : ℝ) - (n : ℝ) ^ k / (Nat.factorial k : ℝ)| ≤
          Cchoose * (n : ℝ) ^ (k - 1) := by
    intro n
    exact (Classical.choose_spec (choose_sub_pow_div_factorial_bound (k := k) hk)).2 n
  have hsecond_nonneg : 0 ≤ ∫ ω, X 0 ω ^ 2 ∂P := by
    refine integral_nonneg ?_
    intro ω
    positivity
  have hAcoeff_nonneg : 0 ≤ Acoeff := by
    dsimp [Acoeff]
    exact mul_nonneg (by positivity) (pow_nonneg hsecond_nonneg _)
  have hprofileIntegrable :
      ∀ a ∈ A, Integrable (fun ω ↦ ∏ i : Fin n, X i ω ^ a i) P := by
    intro a ha
    exact integrable_profileProduct_of_positive
      (X := X) (P := P) hident h_moments hm a (by simpa [A] using ha)
  have hexpand :
      ∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P = Finset.sum A summand := by
    -- Proof comment: expand the even power over `piAntidiag` profiles and exchange the finite sum
    -- with the integral once all profile monomials are known to be integrable.
    calc
      ∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P
          = ∫ ω,
              Finset.sum A (fun a ↦
                (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
                  (∏ i : Fin n, X i ω ^ a i)) ∂P := by
              refine integral_congr_ae <| Filter.Eventually.of_forall fun ω ↦ ?_
              simpa [A, partialSum_eq_sum_univ_fin (X := X) (n := n) (ω := ω), summand] using
                (partialSumPow_eq_sum_piAntidiag_univ (X := X) (m := m) (n := n) (ω := ω))
      _ =
          Finset.sum A (fun a ↦
            ∫ ω,
              (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
                (∏ i : Fin n, X i ω ^ a i) ∂P) := by
            simpa using
              (MeasureTheory.integral_finset_sum
                (μ := P)
                (s := A)
                (f := fun a ω ↦
                  (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
                    (∏ i : Fin n, X i ω ^ a i))
                (fun a ha ↦ (hprofileIntegrable a ha).const_mul _))
      _ = Finset.sum A summand := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            dsimp [summand]
            rw [MeasureTheory.integral_const_mul]
  have hvanishOne :
      Finset.sum (A.filter (fun a ↦ ∃ i : Fin n, a i = 1)) summand = 0 := by
    -- Proof comment: every profile with an exponent `1` contributes a centered first-moment
    -- factor, so its whole mixed moment vanishes.
    refine Finset.sum_eq_zero ?_
    intro a ha
    rcases (Finset.mem_filter.mp ha).2 with ⟨i, hi⟩
    simp [summand, profileMoment_eq_zero_of_hasExponentOne
      (X := X) (P := P) hindep hident h0 (a := a) hi]
  have hsplitNoOne :
      Finset.sum A summand = Finset.sum (A.filter noOne) summand := by
    -- Proof comment: after splitting the profile sum by the presence of an exponent `1`, the
    -- killed block disappears and only the non-singleton profiles remain.
    calc
      Finset.sum A summand
          = Finset.sum (A.filter (fun a ↦ ∃ i : Fin n, a i = 1)) summand +
              Finset.sum (A.filter noOne) summand := by
                simpa [noOne] using
                  (Finset.sum_filter_add_sum_filter_not
                    (s := A) (p := fun a : Fin n → ℕ ↦ ∃ i : Fin n, a i = 1) (f := summand)).symm
      _ = Finset.sum (A.filter noOne) summand := by rw [hvanishOne, zero_add]
  have hsplitPairRemainder :
      Finset.sum (A.filter noOne) summand =
        Finset.sum pairBlock summand + Finset.sum remainderBlock summand := by
    -- Proof comment: split the non-singleton profiles into the maximal-support pair block and the
    -- smaller-support remainder that will be estimated crudely.
    simpa [pairBlock, remainderBlock] using
      (Finset.sum_filter_add_sum_filter_not
        (s := A.filter noOne) (p := fun a : Fin n → ℕ ↦ (supp a).card = k) (f := summand)).symm
  have hpairSupportData :
      ∀ {a : Fin n → ℕ}, a ∈ pairBlock →
        supp a ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ a = pairProfile (supp a) := by
    intro a ha
    have ha_mem : a ∈ A.filter noOne := (Finset.mem_filter.mp ha).1
    have haA : a ∈ A := (Finset.mem_filter.mp ha_mem).1
    have hnoOnePred : noOne a := (Finset.mem_filter.mp ha_mem).2
    have hnoOne :
        ∀ i : Fin n, a i ≠ 1 := by
      intro i hi
      exact hnoOnePred ⟨i, hi⟩
    have hsupp : (supp a).card = k := (Finset.mem_filter.mp ha).2
    simpa [supp] using
      (profile_eq_pairProfile_of_even_sum_support_eq (k := k) (a := a)
        (by simpa [A] using haA) hnoOne hsupp)
  have hpairSummand :
      ∀ {a : Fin n → ℕ}, a ∈ pairBlock →
        summand a =
          (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile (supp a)) : ℝ) *
            (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile (supp a) i ∂P) := by
    intro a ha
    simpa [summand] using congrArg summand (hpairSupportData ha).2
  have hpairBlock :
      Finset.sum pairBlock summand =
        Finset.sum ((Finset.univ : Finset (Fin n)).powersetCard k) (fun s ↦
          (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
            (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P)) := by
    -- Proof comment: use the support map `a ↦ supp a` to transport the maximal-support block
    -- exactly to the pure pair profiles indexed by `k`-subsets.
    refine Finset.sum_bij (fun a _ ↦ supp a) ?_ ?_ ?_ ?_
    · intro a ha
      exact (hpairSupportData ha).1
    · intro a ha b hb hab
      have hsupp_eq : supp a = supp b := by
        simpa using hab
      rw [(hpairSupportData ha).2, (hpairSupportData hb).2, hsupp_eq]
    · intro s hs
      rcases pairProfile_mem_evenPairBlock (k := k) (n := n) hs with ⟨hs_mem, hs_support⟩
      refine ⟨pairProfile s, ?_, ?_⟩
      · simpa [pairBlock, A, noOne, supp, m] using hs_mem
      · simpa [supp] using hs_support
    · intro a ha
      exact hpairSummand ha
  have hpairMain :
      Finset.sum pairBlock summand = Acoeff * (n.choose k : ℝ) := by
    -- Proof comment: after the support bijection, the exact pair block is the previously closed
    -- pure-pair contribution with coefficient `n.choose k`.
    calc
      Finset.sum pairBlock summand
          = Finset.sum ((Finset.univ : Finset (Fin n)).powersetCard k) (fun s ↦
              (Nat.multinomial (Finset.univ : Finset (Fin n)) (pairProfile s) : ℝ) *
                (∫ ω, ∏ i : Fin n, X i ω ^ pairProfile s i ∂P)) := hpairBlock
      _ = Acoeff * (n.choose k : ℝ) := by
            simpa [Acoeff, m] using
              (pairProfilesContribution_eq_chooseMainTerm
                (X := X) (P := P) hindep hident (k := k) (n := n))
  have hremainderSupport :
      ∀ {a : Fin n → ℕ}, a ∈ remainderBlock → (supp a).card ≤ k - 1 := by
    intro a ha
    have ha_mem : a ∈ A.filter noOne := (Finset.mem_filter.mp ha).1
    have haA : a ∈ A := (Finset.mem_filter.mp ha_mem).1
    have hnoOnePred : noOne a := (Finset.mem_filter.mp ha_mem).2
    have hne : (supp a).card ≠ k := (Finset.mem_filter.mp ha).2
    rcases evenProfileTrichotomy (k := k) (a := a) (by simpa [A] using haA) with
      hOne | hPair | hSmall
    · exact False.elim (hnoOnePred hOne)
    · have hPairData :
          supp a ∈ (Finset.univ : Finset (Fin n)).powersetCard k ∧ a = pairProfile (supp a) := by
        simpa [supp] using hPair
      exact False.elim (hne ((Finset.mem_powersetCard.mp hPairData.1).2))
    · simpa [supp] using hSmall
  have hsmallCount_nat :
      smallBlock.card ≤ Csmall * n ^ (k - 1) := by
    -- Proof comment: the previously established support-count bound applies directly to all
    -- profiles with support cardinality at most `k - 1`.
    simpa [smallBlock, A, supp, Csmall, m] using
      (Classical.choose_spec
        (smallSupportPiAntidiag_count_bound (m := m) (r := k - 1) hm) n)
  have hremainderSubset : remainderBlock ⊆ smallBlock := by
    intro a ha
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1,
      hremainderSupport ha⟩
  have hremainderCount_nat :
      remainderBlock.card ≤ Csmall * n ^ (k - 1) := by
    exact (Finset.card_le_card hremainderSubset).trans hsmallCount_nat
  have hremainderCount :
      (((remainderBlock.card : ℕ) : ℝ)) ≤ (Csmall : ℝ) * (n : ℝ) ^ (k - 1) := by
    exact_mod_cast hremainderCount_nat
  have hsummandAbs :
      ∀ {a : Fin n → ℕ}, a ∈ A → |summand a| ≤ E := by
    intro a ha
    have hmult_nonneg :
        0 ≤ (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) := by
      positivity
    calc
      |summand a|
          = (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
              |∫ ω, ∏ i : Fin n, X i ω ^ a i ∂P| := by
                dsimp [summand]
                rw [abs_mul, abs_of_nonneg hmult_nonneg]
      _ ≤ (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) *
            (degreeMomentEnvelope (X := X) (P := P) m ^ m) := by
              exact mul_le_mul_of_nonneg_left
                (absProfileMoment_le_degreeEnvelope
                  (X := X) (P := P) hindep hident h_moments a (by simpa [A] using ha))
                hmult_nonneg
      _ ≤ (Nat.factorial m : ℝ) * (degreeMomentEnvelope (X := X) (P := P) m ^ m) := by
            have hmult_le :
                (Nat.multinomial (Finset.univ : Finset (Fin n)) a : ℝ) ≤
                  (Nat.factorial m : ℝ) := by
              exact_mod_cast
                (multinomial_le_factorial_of_piAntidiag (a := a) (by simpa [A] using ha))
            exact mul_le_mul_of_nonneg_right hmult_le
              (pow_nonneg (degreeMomentEnvelope_nonneg (X := X) (P := P) m) _)
      _ = E := by rfl
  have hremainderAbs :
      |Finset.sum remainderBlock summand| ≤ ((Csmall : ℝ) * E) * (n : ℝ) ^ (k - 1) := by
    -- Proof comment: on the remainder block, bound each profile uniformly by the factorial
    -- envelope and then count how many small-support profiles remain.
    calc
      |Finset.sum remainderBlock summand|
          ≤ Finset.sum remainderBlock (fun a ↦ |summand a|) := by
              simpa using
                (Finset.abs_sum_le_sum_abs
                  (s := remainderBlock) (f := summand))
      _ ≤ Finset.sum remainderBlock (fun _ ↦ E) := by
            refine Finset.sum_le_sum ?_
            intro a ha
            exact hsummandAbs ((Finset.mem_filter.mp (Finset.mem_filter.mp ha).1).1)
      _ = (((remainderBlock.card : ℕ) : ℝ)) * E := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((Csmall : ℝ) * (n : ℝ) ^ (k - 1)) * E := by
            exact mul_le_mul_of_nonneg_right hremainderCount hE_nonneg
      _ = ((Csmall : ℝ) * E) * (n : ℝ) ^ (k - 1) := by
            ring
  have htarget_eq :
      targetTerm = Acoeff * ((n : ℝ) ^ k / (Nat.factorial k : ℝ)) := by
    dsimp [targetTerm, Acoeff, m]
    field_simp
  have hpairGap :
      |Finset.sum pairBlock summand - targetTerm| ≤
        (Acoeff * Cchoose) * (n : ℝ) ^ (k - 1) := by
    -- Proof comment: factor the exact pair contribution against the textbook leading term so
    -- the remaining scalar gap is exactly the `choose` versus `n^k / k!` estimate.
    rw [hpairMain, htarget_eq]
    calc
      |Acoeff * (n.choose k : ℝ) - Acoeff * ((n : ℝ) ^ k / (Nat.factorial k : ℝ))|
          = |Acoeff * ((n.choose k : ℝ) - (n : ℝ) ^ k / (Nat.factorial k : ℝ))| := by
              congr 1
              ring
      _ = Acoeff * |(n.choose k : ℝ) - (n : ℝ) ^ k / (Nat.factorial k : ℝ)| := by
            rw [abs_mul, abs_of_nonneg hAcoeff_nonneg]
      _ ≤ Acoeff * (Cchoose * (n : ℝ) ^ (k - 1)) := by
            exact mul_le_mul_of_nonneg_left (hchooseBound n) hAcoeff_nonneg
      _ = (Acoeff * Cchoose) * (n : ℝ) ^ (k - 1) := by
            ring
  have hmain :
      |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P - targetTerm| ≤
        d (2 * k) * (n : ℝ) ^ (k - 1) := by
    -- Proof comment: after replacing the maximal-support block by the exact pair contribution,
    -- the target error splits into the `choose` gap and the small-support remainder estimate.
    calc
      |∫ ω, (Finset.sum (Finset.range n) (fun i ↦ X i ω)) ^ m ∂P - targetTerm|
          = |((Finset.sum pairBlock summand) - targetTerm) +
              Finset.sum remainderBlock summand| := by
                rw [hexpand, hsplitNoOne, hsplitPairRemainder]
                ring
      _ ≤ |(Finset.sum pairBlock summand) - targetTerm| +
            |Finset.sum remainderBlock summand| := by
            simpa using
                abs_add_le
                  ((Finset.sum pairBlock summand) - targetTerm)
                  (Finset.sum remainderBlock summand)
      _ ≤ (Acoeff * Cchoose) * (n : ℝ) ^ (k - 1) +
            ((Csmall : ℝ) * E) * (n : ℝ) ^ (k - 1) := by
              exact add_le_add hpairGap hremainderAbs
      _ = (((Csmall : ℝ) * E) + Acoeff * Cchoose) * (n : ℝ) ^ (k - 1) := by
            ring
      _ = d (2 * k) * (n : ℝ) ^ (k - 1) := by
            rw [hd_eval]
  simpa [m, targetTerm] using hmain

/-- Helper for Exercise 15.4.6: a finite absolute second moment puts a real random variable in
`L²`. -/
lemma memLpTwoOfFiniteSecondAbsoluteMoment {Z : Ω → ℝ}
    (hZ : AEStronglyMeasurable Z P)
    (h2 : Integrable (fun ω ↦ |Z ω| ^ (2 : ℕ)) P) :
    MemLp Z 2 P := by
  -- Proof comment: for real-valued functions, membership in `L²` is exactly integrability of the
  -- square. The given absolute-square hypothesis is the same statement after `sq_abs`.
  rw [memLp_two_iff_integrable_sq hZ]
  simpa [sq_abs] using h2

-- Proof sketch: apply the characteristic-function derivative formula from Theorem 15.31(i) to a
-- standard Gaussian law and evaluate the odd derivatives at the origin.
/-- Standard Gaussian odd moments vanish. -/
theorem gaussianReal_odd_moments_eq_zero (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k + 1) ∂P' = 0 := by
  intro k
  let γ : Measure ℝ := gaussianReal (0 : ℝ) (1 : NNReal)
  have htransport :
      ∫ ω, Y ω ^ (2 * k + 1) ∂P' = ∫ x, x ^ (2 * k + 1) ∂γ := by
    -- Proof comment: move the odd moment to the standard Gaussian law carried by `Y`.
    simpa [γ, Function.comp] using
      (hY.integral_comp
        (f := fun x : ℝ ↦ x ^ (2 * k + 1))
        ((continuous_pow _).aestronglyMeasurable))
  have hsymm : γ.map (fun x : ℝ ↦ -x) = γ := by
    simpa [γ] using
      (ProbabilityTheory.gaussianReal_map_neg (μ := (0 : ℝ)) (v := (1 : NNReal)))
  have hEq :
      ∫ x, x ^ (2 * k + 1) ∂γ = ∫ x, (-x) ^ (2 * k + 1) ∂γ := by
    -- Proof comment: reflecting the centered Gaussian leaves its law unchanged.
    calc
      ∫ x, x ^ (2 * k + 1) ∂γ
          = ∫ x, x ^ (2 * k + 1) ∂Measure.map (fun x : ℝ ↦ -x) γ := by
              simpa [hsymm]
      _ = ∫ x, (-x) ^ (2 * k + 1) ∂γ := by
            rw [MeasureTheory.integral_map (by fun_prop) (by fun_prop)]
  have hNeg :
      ∫ x, (-x) ^ (2 * k + 1) ∂γ = -∫ x, x ^ (2 * k + 1) ∂γ := by
    -- Proof comment: the integrand is odd, so negation flips the sign of the integral.
    have hfun :
        (fun x : ℝ ↦ (-x) ^ (2 * k + 1)) = fun x ↦ -x ^ (2 * k + 1) := by
      funext x
      calc
        (-x) ^ (2 * k + 1) = (((-1 : ℝ) * x) ^ (2 * k + 1)) := by
          congr 1
          ring
        _ = (-1 : ℝ) ^ (2 * k + 1) * x ^ (2 * k + 1) := by rw [mul_pow]
        _ = (-1 : ℝ) * x ^ (2 * k + 1) := by
              rw [pow_add, pow_mul]
              norm_num
        _ = -x ^ (2 * k + 1) := by ring
    rw [hfun, MeasureTheory.integral_neg]
  have hzero : ∫ x, x ^ (2 * k + 1) ∂γ = 0 := by
    linarith [hEq.trans hNeg]
  exact htransport.trans hzero

/-- Helper for Exercise 15.4.6: the Gaussian factorial ratio agrees with the odd double
factorial. -/
lemma gaussianEvenFactorialRatio_eq_oddDoubleFactorial (k : ℕ) :
    (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) =
      (Nat.doubleFactorial (2 * k - 1) : ℝ) := by
  cases k with
  | zero =>
      -- Proof comment: the zeroth even moment constant is `1`, which matches `(-1)‼ = 1`.
      norm_num
  | succ k =>
      have hfacNat :
          Nat.factorial (2 * (k + 1)) =
            Nat.doubleFactorial (2 * (k + 1)) * Nat.doubleFactorial (2 * k + 1) := by
        -- Proof comment: normalize `(2k + 2)!` through the canonical factorial/double-factorial
        -- identity at the odd predecessor `2k + 1`.
        simpa [two_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm, Nat.succ_eq_add_one,
          mul_add, add_mul] using Nat.factorial_eq_mul_doubleFactorial (2 * k + 1)
      have hfac :
          ((Nat.factorial (2 * (k + 1)) : ℕ) : ℝ) =
            (Nat.doubleFactorial (2 * (k + 1)) : ℝ) *
              (Nat.doubleFactorial (2 * k + 1) : ℝ) := by
        exact_mod_cast hfacNat
      have hdouble :
          (Nat.doubleFactorial (2 * (k + 1)) : ℝ) =
            ((2 : ℝ) ^ (k + 1)) * (Nat.factorial (k + 1) : ℝ) := by
        -- Proof comment: the even double factorial is exactly `2^(k+1) * (k+1)!`.
        exact_mod_cast (Nat.doubleFactorial_two_mul (k + 1))
      rw [show 2 * (k + 1) - 1 = 2 * k + 1 by omega]
      rw [hfac, hdouble]
      field_simp

/-- Helper for Exercise 15.4.6: the Gamma-form scalar from the positive-half-line Gaussian moment
normalizes to the half factorial-ratio coefficient. -/
lemma gaussianHalfLineGammaScalar_eq_halfFactorialRatio (k : ℕ) :
    (Real.sqrt (2 * Real.pi))⁻¹ *
        (((1 / 2 : ℝ) ^ (-(((2 * k : ℝ) + 1) / 2))) * (1 / 2 : ℝ) *
          Real.Gamma ((k : ℝ) + 1 / 2)) =
      (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ)) := by
  -- Proof comment: rewrite the Gamma value at `k + 1/2`, convert the target coefficient to the
  -- odd double-factorial form divided by `2`, and then simplify the remaining square-root scalar.
  rw [Real.Gamma_nat_add_half k]
  have hratioHalf :
      (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ)) =
        (Nat.doubleFactorial (2 * k - 1) : ℝ) / 2 := by
    calc
      (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ))
          = ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ))) / 2 := by
              rw [pow_succ']
              field_simp
      _ = (Nat.doubleFactorial (2 * k - 1) : ℝ) / 2 := by
            rw [gaussianEvenFactorialRatio_eq_oddDoubleFactorial]
  rw [hratioHalf]
  have hpow :
      ((1 / 2 : ℝ) ^ (-(((2 * k : ℝ) + 1) / 2))) = (2 : ℝ) ^ (((2 * k : ℝ) + 1) / 2) := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num]
    rw [Real.inv_rpow (by positivity), Real.rpow_neg (by positivity), inv_inv]
  have hpowSplit :
      (2 : ℝ) ^ (((2 * k : ℝ) + 1) / 2) = (2 : ℝ) ^ k * Real.sqrt 2 := by
    rw [show (((2 * k : ℝ) + 1) / 2) = (k : ℝ) + 1 / 2 by ring]
    rw [Real.rpow_add (by positivity)]
    rw [Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  rw [hpow, hpowSplit]
  have hsqrt :
      Real.sqrt (2 * Real.pi) = Real.sqrt 2 * Real.sqrt Real.pi := by
    rw [mul_comm, Real.sqrt_mul (show 0 ≤ Real.pi by positivity)]
    ring
  rw [hsqrt]
  have hsqrtTwo_ne : Real.sqrt (2 : ℝ) ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 (by positivity)
  have hsqrtPi_ne : Real.sqrt Real.pi ≠ 0 := by
    exact Real.sqrt_ne_zero'.2 Real.pi_pos
  field_simp [hsqrtTwo_ne, hsqrtPi_ne]

/-- Helper for Exercise 15.4.6: the positive-half-line contribution of the `2k`th standard
Gaussian moment is exactly half of the factorial-ratio constant. -/
lemma gaussianEvenMomentIntegral_Ioi_eq_halfFactorialRatio (k : ℕ) :
    ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * gaussianPDFReal 0 1 x =
      (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ)) := by
  have hq : (-1 : ℝ) < (2 * k : ℝ) := by
    nlinarith
  -- Proof comment: rewrite the density integral into the standard Gamma-form integral on
  -- `Ioi 0`, then discharge the remaining constant with the dedicated scalar bridge.
  calc
    ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * gaussianPDFReal 0 1 x
        = ∫ x in Set.Ioi (0 : ℝ),
            (Real.sqrt (2 * Real.pi))⁻¹ *
              (x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))) := by
              rw [gaussianPDFReal_def]
              refine setIntegral_congr_fun measurableSet_Ioi ?_
              intro x hx
              -- Proof comment: on the positive half-line, the Gaussian density is exactly the
              -- scalar multiple of `x^(2k) * exp (-(1/2) * x^2)` used by the Gamma integral.
              calc
                x ^ (2 * k) * ((√(2 * Real.pi * ↑1))⁻¹ * Real.exp (-(x - 0) ^ 2 / (2 * ↑1)))
                    = (√(2 * Real.pi))⁻¹ * (x ^ (2 * k) * Real.exp (-(1 / 2) * x ^ 2)) := by
                        field_simp
                        ring
                _ = (Real.sqrt (2 * Real.pi))⁻¹ *
                      (x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ))) := by
                        rw [← Real.rpow_natCast x (2 * k), ← Real.rpow_natCast x 2]
                        rfl
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          ∫ x in Set.Ioi (0 : ℝ), x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(1 / 2 : ℝ) * x ^ (2 : ℝ)) := by
            rw [integral_const_mul]
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          (((1 / 2 : ℝ) ^ (-(((2 * k : ℝ) + 1) / 2))) * (1 / 2 : ℝ) *
            Real.Gamma (((2 * k : ℝ) + 1) / 2)) := by
            have hInt :=
              integral_rpow_mul_exp_neg_mul_rpow (p := (2 : ℝ)) (q := (2 * k : ℝ))
                (b := (1 / 2 : ℝ)) zero_lt_two hq (by positivity)
            have hExp : (((-1 : ℝ) + -(2 * k : ℝ)) / 2) = -(((2 * k : ℝ) + 1) / 2) := by
              ring
            congr 1
            simpa [hExp] using hInt
    _ = (Real.sqrt (2 * Real.pi))⁻¹ *
          (((1 / 2 : ℝ) ^ (-(((2 * k : ℝ) + 1) / 2))) * (1 / 2 : ℝ) *
            Real.Gamma ((k : ℝ) + 1 / 2)) := by
            congr 2
            ring
    _ = (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ)) := by
          rw [gaussianHalfLineGammaScalar_eq_halfFactorialRatio]

/-- Helper for Exercise 15.4.6: the even moments of the standard Gaussian density are the
factorial-ratio constants `(2k)! / (2^k k!)`. -/
lemma standardGaussianEvenMoment_eq_factorial_ratio (k : ℕ) :
    ∫ x : ℝ, x ^ (2 * k) ∂(gaussianReal 0 1) =
      (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := by
  -- Proof comment: rewrite the Gaussian expectation as a density integral, then use evenness to
  -- reduce the whole-line integral to twice the positive-half-line integral.
  have hpdf_abs : ∀ x : ℝ, gaussianPDFReal 0 1 |x| = gaussianPDFReal 0 1 x := by
    intro x
    simp [ProbabilityTheory.gaussianPDFReal_def, sq_abs]
  calc
    ∫ x : ℝ, x ^ (2 * k) ∂(gaussianReal 0 1)
        = ∫ x : ℝ, x ^ (2 * k) * gaussianPDFReal 0 1 x := by
            simpa [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
              (ProbabilityTheory.integral_gaussianReal_eq_integral_smul
                (μ := (0 : ℝ)) (v := (1 : NNReal))
                (f := fun x : ℝ ↦ x ^ (2 * k)) one_ne_zero)
    _ = ∫ x : ℝ, (fun y : ℝ ↦ y ^ (2 * k) * gaussianPDFReal 0 1 y) |x| := by
          refine integral_congr_ae ?_
          filter_upwards with x
          have hpow_abs : x ^ (2 * k) = |x| ^ (2 * k) := by
            calc
              x ^ (2 * k) = (x ^ 2) ^ k := by rw [← pow_mul]
              _ = (|x| ^ 2) ^ k := by rw [sq_abs]
              _ = |x| ^ (2 * k) := by rw [pow_mul]
          rw [hpow_abs, hpdf_abs x]
    _ = 2 * ∫ x in Set.Ioi (0 : ℝ), x ^ (2 * k) * gaussianPDFReal 0 1 x := by
          simpa using
            (integral_comp_abs
              (f := fun y : ℝ ↦ y ^ (2 * k) * gaussianPDFReal 0 1 y))
    _ = 2 *
          ((Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ (k + 1)) * (Nat.factorial k : ℝ))) := by
          rw [gaussianEvenMomentIntegral_Ioi_eq_halfFactorialRatio]
    _ = (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := by
          rw [pow_succ']
          field_simp

-- Proof sketch: differentiate the standard Gaussian characteristic function at `0`, then compare
-- the resulting even derivatives with the moment formula from Theorem 15.31(i).
/-- Standard Gaussian even moments are the factorial-ratio constants
`(2k)! / (2^k k!)`. -/
theorem gaussianReal_even_moments_eq_factorial_ratio (hY : HasLaw Y (gaussianReal 0 1) P') :
    ∀ k : ℕ,
      ∫ ω, Y ω ^ (2 * k) ∂P' =
        (Nat.factorial (2 * k) : ℝ) / (((2 : ℝ) ^ k) * (Nat.factorial k : ℝ)) := by
  intro k
  have htransport :
      ∫ ω, Y ω ^ (2 * k) ∂P' = ∫ x : ℝ, x ^ (2 * k) ∂(gaussianReal 0 1) := by
    -- Proof comment: transport the even moment along the law identity supplied by `hY`.
    simpa [Function.comp] using
      (hY.integral_comp
        (f := fun x : ℝ ↦ x ^ (2 * k))
        ((continuous_pow _).aestronglyMeasurable))
  exact htransport.trans (standardGaussianEvenMoment_eq_factorial_ratio k)

-- Proof sketch: combine the moment bounds from the odd and even expansions with the Gaussian
-- moment identities, use the moment-convergence criterion from Exercise 15.4.5, and then pass
-- from convergence of moments to convergence in distribution against a standard Gaussian limit law.
/-- Centered iid real variables with finite absolute moments of every order have standardized
partial sums converging in distribution to the standard Gaussian law. -/
theorem standardizedPartialSum_tendstoInDistribution_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0)
    (hY : HasLaw Y (gaussianReal 0 1) P') :
    TendstoInDistribution (fun n ↦ standardizedPartialSum P X n) atTop Y (fun _ ↦ P) P' := by
  let _ := h0
  have hX_memLp : MemLp (X 0) 2 P := by
    -- Proof comment: the `k = 2` absolute moment hypothesis is exactly the `L²` input required
    -- by the imported CLT theorem.
    apply memLpTwoOfFiniteSecondAbsoluteMoment
    · exact ((hident 0).aemeasurable_fst).aestronglyMeasurable
    · simpa using h_moments 2
  refine
    { forall_aemeasurable := fun n ↦
        aemeasurable_standardizedPartialSum P X (fun m ↦ (hident m).aemeasurable_fst) n
      aemeasurable_limit := hY.aemeasurable
      tendsto := ?_ }
  -- Proof comment: reuse the owner law-level CLT and rewrite the limit law using `hY`.
  simpa [hY.map_eq] using
    (standardizedPartialSumLaw_tendsto_standardGaussian P X hX_memLp hvar hindep hident)

-- Proof sketch: first obtain convergence in distribution of `standardizedPartialSum P X n` to a
-- standard Gaussian variable from the previous theorem, then rewrite this as convergence of the
-- associated pushforward probability measures in
-- `ProbabilityMeasure ℝ`.
/-- Consequence for Exercise 15.4.6 item (iii): if `X₁, X₂, ...` are iid centered real random
variables with finite absolute moments of every order and nonzero variance, then the laws of the
standardized partial sums `S_n^*` converge weakly to the standard Gaussian law. -/
theorem standardizedPartialSumLaw_tendsto_standardGaussian_of_iid_all_moments
    (hindep : iIndepFun X P)
    (hident : ∀ n, IdentDistrib (X n) (X 0) P P)
    (h0 : ∫ ω, X 0 ω ∂P = 0)
    (h_moments : ∀ k : ℕ, Integrable (fun ω ↦ |X 0 ω| ^ k) P)
    (hvar : Var[X 0; P] ≠ 0) :
    Tendsto
      (fun n ↦
        ProbabilityMeasure.map ⟨P, inferInstance⟩
          (aemeasurable_standardizedPartialSum P X (fun n ↦ (hident n).aemeasurable_fst) n))
      atTop
      (𝓝 ⟨gaussianReal 0 1, inferInstance⟩) := by
  let _ := h0
  have hX_memLp : MemLp (X 0) 2 P := by
    -- Proof comment: only the second absolute moment is needed to invoke the imported CLT.
    apply memLpTwoOfFiniteSecondAbsoluteMoment
    · exact ((hident 0).aemeasurable_fst).aestronglyMeasurable
    · simpa using h_moments 2
  -- Proof comment: this is exactly the owner CLT theorem once the `L²` hypothesis is packaged.
  simpa using
    (standardizedPartialSumLaw_tendsto_standardGaussian P X hX_memLp hvar hindep hident)
