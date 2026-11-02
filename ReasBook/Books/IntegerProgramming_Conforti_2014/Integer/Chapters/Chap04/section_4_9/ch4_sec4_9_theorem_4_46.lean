import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_26
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_18.ch3_sec3_18_exercise_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_1.ch4_sec4_1_theorem_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators
open scoped IntegerVectorNotation

-- Domain-style sampling for this refine pass:
-- * primitive owner reused from the project: `is_zero_one_vector`
-- * source-facing owners introduced here: `one_coordinate_count`, `even_zero_one_vectors`,
--   `odd_set_inequality`, `odd_set_polyhedron`
-- * derived API only: convexity and containment lemmas for those owners

/-- The number of coordinates of `x` that are equal to `1`. -/
noncomputable def one_coordinate_count {n : ℕ} (x : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter fun i : Fin n ↦ x i = 1).card

/-- The `0,1` vectors in `ℝ^n` with an even number of `1` coordinates. -/
def even_zero_one_vectors (n : ℕ) : Set (Fin n → ℝ) :=
  {x | is_zero_one_vector x ∧ Even (one_coordinate_count x)}

/-- The `0,1` vectors in `ℝ^n` with an odd number of `1` coordinates. -/
def odd_zero_one_vectors (n : ℕ) : Set (Fin n → ℝ) :=
  {x | is_zero_one_vector x ∧ Odd (one_coordinate_count x)}

/-- The odd-set inequality associated with the subset `S`. -/
def odd_set_inequality {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) : Prop :=
  S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - 1

/-- The odd-cardinality subsets of `Fin n`, used to index the odd-set halfspaces. -/
abbrev odd_subset (n : ℕ) :=
  {S : Finset (Fin n) // Odd S.card}

/-- The even-cardinality subsets of `Fin n`, used for the odd-parity companion system. -/
abbrev even_subset (n : ℕ) :=
  {S : Finset (Fin n) // Even S.card}

/-- The odd-set polyhedron: the box intersected with all odd-set halfspaces. -/
def odd_set_polyhedron (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (0 : Fin n → ℝ) 1 ∩ ⋂ S : odd_subset n, {x : Fin n → ℝ | odd_set_inequality S.1 x}

/-- The even-set companion polyhedron: the same box intersected with all even-set halfspaces. -/
def even_set_polyhedron (n : ℕ) : Set (Fin n → ℝ) :=
  Set.Icc (0 : Fin n → ℝ) 1 ∩ ⋂ S : even_subset n, {x : Fin n → ℝ | odd_set_inequality S.1 x}

/-- Helper for Theorem 4.46: regard a subset of `Fin n` inside `Fin (n + 1)` via `castSucc`. -/
def castSuccFinset {n : ℕ} (S : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  S.map ⟨Fin.castSucc, fun _ _ h ↦ Fin.castSucc_injective _ h⟩

/-- Helper for Theorem 4.46: the `castSucc`-coordinates of a subset of `Fin (n + 1)`. -/
def prefixFinset {n : ℕ} (T : Finset (Fin (n + 1))) : Finset (Fin n) :=
  Finset.univ.filter fun i : Fin n ↦ i.castSucc ∈ T

/-- Helper for Theorem 4.46: on a `0/1` vector, a finite coordinate sum is the cardinality of the
coordinates equal to `1` on that finite set. -/
lemma sum_eq_card_filter_of_zero_one {n : ℕ} (x : Fin n → ℝ) (S : Finset (Fin n))
    (hx : is_zero_one_vector x) :
    S.sum x = ((S.filter fun i ↦ x i = 1).card : ℝ) := by
  -- Replace each coordinate by the corresponding `if`-indicator and then evaluate the sum of
  -- indicators as a cardinality.
  calc
    S.sum x = ∑ i ∈ S, if x i = 1 then (1 : ℝ) else 0 := by
      refine Finset.sum_congr rfl ?_
      intro i hi
      rcases hx i with h0 | h1
      · simp [h0]
      · simp [h1]
    _ = ((S.filter fun i ↦ x i = 1).card : ℝ) := by
      rw [Finset.sum_boole]

/-- Helper for Theorem 4.46: adding a last coordinate `0` preserves the `0/1` property. -/
lemma is_zero_one_vector_snoc_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    is_zero_one_vector (Fin.snoc x 0) := by
  -- Split the coordinates into the old ones and the new last coordinate.
  unfold is_zero_one_vector at hx ⊢
  rw [Fin.forall_fin_succ']
  constructor
  · intro i
    simpa using hx i
  · left
    simp

/-- Helper for Theorem 4.46: adding a last coordinate `1` preserves the `0/1` property. -/
lemma is_zero_one_vector_snoc_one {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    is_zero_one_vector (Fin.snoc x 1) := by
  -- Split the coordinates into the old ones and the new last coordinate.
  unfold is_zero_one_vector at hx ⊢
  rw [Fin.forall_fin_succ']
  constructor
  · intro i
    simpa using hx i
  · right
    simp

/-- Helper for Theorem 4.46: `Fin.snoc` rebuilds a tuple from its prefix and last coordinate. -/
lemma snoc_prefix_last {n : ℕ} (y : Fin (n + 1) → ℝ) :
    Fin.snoc (fun i : Fin n ↦ y i.castSucc) (y (Fin.last n)) = y := by
  -- Check the equality on the prefix coordinates and on the new last coordinate.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · simp
  · simp

/-- Helper for Theorem 4.46: a `castSucc`-embedded finite set preserves membership. -/
lemma mem_castSuccFinset {n : ℕ} {S : Finset (Fin n)} {i : Fin n} :
    i.castSucc ∈ castSuccFinset S ↔ i ∈ S := by
  -- Membership in the mapped finset is exactly membership before applying the embedding.
  simp [castSuccFinset]

/-- Helper for Theorem 4.46: membership in `prefixFinset` is exactly membership of the
corresponding `castSucc` index in the ambient subset. -/
lemma mem_prefixFinset {n : ℕ} {T : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ prefixFinset T ↔ i.castSucc ∈ T := by
  -- `prefixFinset` is defined by filtering the universal finite set by the `castSucc` membership
  -- test, so the membership condition simplifies directly.
  simp [prefixFinset]

/-- Helper for Theorem 4.46: a subset of `Fin (n + 1)` is recovered from its prefix part, with
the last index reinserted exactly when it was present originally. -/
lemma prefixFinset_last_split {n : ℕ} (T : Finset (Fin (n + 1))) :
    ((Fin.last n ∉ T) → castSuccFinset (prefixFinset T) = T) ∧
      ((Fin.last n ∈ T) → insert (Fin.last n) (castSuccFinset (prefixFinset T)) = T) := by
  constructor
  · intro hlast
    -- If the last index is absent, every element of `T` already lies in the `castSucc` image of
    -- its prefix coordinates.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · constructor
      · intro hi
        exact (mem_prefixFinset).1 ((mem_castSuccFinset).1 hi)
      · intro hi
        exact (mem_castSuccFinset).2 ((mem_prefixFinset).2 hi)
    · constructor
      · intro hi
        simp [castSuccFinset] at hi
      · intro hi
        exact False.elim (hlast hi)
  · intro hlast
    -- If the last index is present, the same prefix reconstruction works after inserting it back.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · constructor
      · intro hi
        have hi' : j.castSucc ∈ castSuccFinset (prefixFinset T) := by
          simpa [Fin.castSucc_ne_last j] using hi
        exact (mem_prefixFinset).1 ((mem_castSuccFinset).1 hi')
      · intro hi
        have hi' : j.castSucc ∈ castSuccFinset (prefixFinset T) := by
          exact (mem_castSuccFinset).2 ((mem_prefixFinset).2 hi)
        simp [Fin.castSucc_ne_last j, hi']
    · constructor
      · intro _
        exact hlast
      · intro _
        simp

/-- Helper for Theorem 4.46: the new last coordinate does not belong to a `castSucc` image. -/
lemma last_not_mem_castSuccFinset {n : ℕ} (S : Finset (Fin n)) :
    Fin.last n ∉ castSuccFinset S := by
  -- Every `castSucc` value is strictly smaller than the new last coordinate.
  intro h
  simp [castSuccFinset] at h

/-- Helper for Theorem 4.46: `castSucc` preserves the size of a finite subset. -/
lemma card_castSuccFinset {n : ℕ} (S : Finset (Fin n)) :
    (castSuccFinset S).card = S.card := by
  -- Mapping along an embedding does not change cardinality.
  simp [castSuccFinset]

/-- Helper for Theorem 4.46: summing a `snoc` tuple over a `castSucc`-embedded subset recovers the
original sum. -/
lemma sum_castSuccFinset_snoc {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (r : ℝ) :
    (castSuccFinset S).sum (Fin.snoc x r) = S.sum x := by
  -- Every embedded index evaluates through `Fin.snoc` to the original coordinate.
  classical
  refine Finset.induction_on S ?_ ?_
  · simp [castSuccFinset]
  · intro i S hi hS
    simp [castSuccFinset, hi]

/-- Helper for Theorem 4.46: the complement of a `castSucc` image contributes the prefix
complement and the last coordinate. -/
lemma sum_compl_castSuccFinset_snoc {n : ℕ} (S : Finset (Fin n)) (x : Fin n → ℝ) (r : ℝ) :
    (Finset.univ \ castSuccFinset S).sum (Fin.snoc x r) = (Finset.univ \ S).sum x + r := by
  -- Compare the partition equalities on `Fin (n + 1)` and on `Fin n`.
  have hsucc :
      (Finset.univ \ castSuccFinset S).sum (Fin.snoc x r) + (castSuccFinset S).sum (Fin.snoc x r) =
        Finset.univ.sum (Fin.snoc x r) := by
    exact Finset.sum_sdiff (Finset.subset_univ (castSuccFinset S))
  have hprefix :
      (Finset.univ \ S).sum x + S.sum x = Finset.univ.sum x := by
    exact Finset.sum_sdiff (Finset.subset_univ S)
  rw [sum_castSuccFinset_snoc] at hsucc
  rw [Fin.sum_univ_castSucc] at hsucc
  have hsucc' :
      (Finset.univ \ castSuccFinset S).sum (Fin.snoc x r) + S.sum x =
        Finset.univ.sum x + r := by
    simpa using hsucc
  linarith

/-- Helper for Theorem 4.46: every even `0/1` vector satisfies each odd-set inequality. -/
lemma odd_set_inequality_of_even_zero_one_vector {n : ℕ} {x : Fin n → ℝ} {S : Finset (Fin n)}
    (hx : is_zero_one_vector x)
    (h_even : Even (one_coordinate_count x))
    (hS_odd : Odd S.card) :
    odd_set_inequality S x := by
  classical
  let a : ℕ := (S.filter fun i ↦ x i = 1).card
  let b : ℕ := ((Finset.univ \ S).filter fun i ↦ x i = 1).card
  have hsumS : S.sum x = (a : ℝ) := by
    simpa [a] using sum_eq_card_filter_of_zero_one x S hx
  have hsumSc : (Finset.univ \ S).sum x = (b : ℝ) := by
    simpa [b] using sum_eq_card_filter_of_zero_one x (Finset.univ \ S) hx
  have hsplit :
      a + b = one_coordinate_count x := by
    -- The `1`-coordinates split into those inside `S` and those outside `S`.
    have hfilterS :
        (Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ i ∈ S) =
          S.filter fun i ↦ x i = 1 := by
      ext i
      simp [and_comm]
    have hfilterSc :
        (Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ ¬ i ∈ S) =
          (Finset.univ \ S).filter fun i ↦ x i = 1 := by
      ext i
      simp [Finset.sdiff_eq_filter, and_comm]
    have hsplit_raw :
        ((Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ i ∈ S)).card +
            ((Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ ¬ i ∈ S)).card =
          (Finset.univ.filter fun i : Fin n ↦ x i = 1).card := by
      let T : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ x i = 1
      simpa [T] using
        (show (T.filter fun i : Fin n ↦ i ∈ S).card +
            (T.filter fun i : Fin n ↦ ¬ i ∈ S).card = T.card from
          T.card_filter_add_card_filter_not fun i : Fin n ↦ i ∈ S)
    rw [hfilterS, hfilterSc] at hsplit_raw
    unfold a b one_coordinate_count
    simpa using hsplit_raw
  have ha_le : a ≤ S.card := by
    simpa [a] using Finset.card_filter_le S (fun i : Fin n ↦ x i = 1)
  unfold odd_set_inequality
  rw [hsumS, hsumSc]
  by_cases hlt : a < S.card
  · -- If strictly fewer than `|S|` coordinates inside `S` are equal to `1`, the inequality is
    -- immediate from the trivial upper bound `a ≤ |S| - 1`.
    have hS_pos : 0 < S.card := hS_odd.pos
    have hS_one : 1 ≤ S.card := Nat.succ_le_of_lt hS_pos
    have ha_nat : a ≤ S.card - 1 := Nat.le_pred_of_lt hlt
    have ha_real : (a : ℝ) ≤ (S.card : ℝ) - 1 := by
      have ha_real' : (a : ℝ) ≤ (((S.card - 1 : ℕ) : ℝ)) := by
        exact_mod_cast ha_nat
      have hsub_add_nat : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hS_one
      have hsub_add : (((S.card - 1 : ℕ) : ℝ)) + 1 = S.card := by
        simpa [Nat.cast_add] using congrArg (fun t : ℕ ↦ (t : ℝ)) hsub_add_nat
      linarith
    have hb_nonneg : (0 : ℝ) ≤ b := by positivity
    linarith
  · -- If all points of `S` are `1`, parity forces at least one additional `1` outside `S`.
    have ha_eq : a = S.card := le_antisymm ha_le (le_of_not_gt hlt)
    have hb_ne_zero : b ≠ 0 := by
      intro hb_zero
      have h_even_card : Even S.card := by
        have h_even_ab : Even (a + b) := by
          rw [← hsplit] at h_even
          exact h_even
        rwa [ha_eq, hb_zero, add_zero] at h_even_ab
      exact (Nat.not_even_iff_odd.mpr hS_odd) h_even_card
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
    have hb_real : (0 : ℝ) < b := by
      exact_mod_cast hb_pos
    have ha_real : (a : ℝ) = S.card := by
      exact_mod_cast ha_eq
    have hb_one : (1 : ℝ) ≤ b := by
      exact_mod_cast (Nat.succ_le_of_lt hb_pos)
    linarith

/-- Helper for Theorem 4.46: a `0/1` vector satisfies the inequality indexed by any subset of the
opposite parity. -/
lemma odd_set_inequality_of_zero_one_vector_of_opposite_parity
    {n : ℕ} {x : Fin n → ℝ} {S : Finset (Fin n)}
    (hx : is_zero_one_vector x)
    (hparity :
      (Even (one_coordinate_count x) ∧ Odd S.card) ∨
        (Odd (one_coordinate_count x) ∧ Even S.card)) :
    odd_set_inequality S x := by
  classical
  let a : ℕ := (S.filter fun i ↦ x i = 1).card
  let b : ℕ := ((Finset.univ \ S).filter fun i ↦ x i = 1).card
  have hsumS : S.sum x = (a : ℝ) := by
    simpa [a] using sum_eq_card_filter_of_zero_one x S hx
  have hsumSc : (Finset.univ \ S).sum x = (b : ℝ) := by
    simpa [b] using sum_eq_card_filter_of_zero_one x (Finset.univ \ S) hx
  have hsplit :
      a + b = one_coordinate_count x := by
    -- The `1`-coordinates split into those inside `S` and those outside `S`.
    have hfilterS :
        (Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ i ∈ S) =
          S.filter fun i ↦ x i = 1 := by
      ext i
      simp [and_comm]
    have hfilterSc :
        (Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ ¬ i ∈ S) =
          (Finset.univ \ S).filter fun i ↦ x i = 1 := by
      ext i
      simp [Finset.sdiff_eq_filter, and_comm]
    have hsplit_raw :
        ((Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ i ∈ S)).card +
            ((Finset.univ.filter fun i : Fin n ↦ x i = 1).filter (fun i ↦ ¬ i ∈ S)).card =
          (Finset.univ.filter fun i : Fin n ↦ x i = 1).card := by
      let T : Finset (Fin n) := Finset.univ.filter fun i : Fin n ↦ x i = 1
      simpa [T] using
        (show (T.filter fun i : Fin n ↦ i ∈ S).card +
            (T.filter fun i : Fin n ↦ ¬ i ∈ S).card = T.card from
          T.card_filter_add_card_filter_not fun i : Fin n ↦ i ∈ S)
    rw [hfilterS, hfilterSc] at hsplit_raw
    unfold a b one_coordinate_count
    simpa using hsplit_raw
  have ha_le : a ≤ S.card := by
    simpa [a] using Finset.card_filter_le S (fun i : Fin n ↦ x i = 1)
  unfold odd_set_inequality
  rw [hsumS, hsumSc]
  by_cases hlt : a < S.card
  · -- Strict inequality on the number of `1`-coordinates inside `S` gives the desired bound.
    have hS_pos : 0 < S.card := Nat.zero_lt_of_lt hlt
    have hS_one : 1 ≤ S.card := Nat.succ_le_of_lt hS_pos
    have ha_nat : a ≤ S.card - 1 := Nat.le_pred_of_lt hlt
    have ha_real : (a : ℝ) ≤ (S.card : ℝ) - 1 := by
      have ha_real' : (a : ℝ) ≤ (((S.card - 1 : ℕ) : ℝ)) := by
        exact_mod_cast ha_nat
      have hsub_add_nat : S.card - 1 + 1 = S.card := Nat.sub_add_cancel hS_one
      have hsub_add : (((S.card - 1 : ℕ) : ℝ)) + 1 = S.card := by
        simpa [Nat.cast_add] using congrArg (fun t : ℕ ↦ (t : ℝ)) hsub_add_nat
      linarith
    have hb_nonneg : (0 : ℝ) ≤ b := by positivity
    linarith
  · -- If every coordinate in `S` is `1`, parity forces at least one `1` outside `S`.
    have ha_eq : a = S.card := le_antisymm ha_le (le_of_not_gt hlt)
    have hb_ne_zero : b ≠ 0 := by
      intro hb_zero
      rcases hparity with hpair | hpair
      · have h_even_card : Even S.card := by
          have h_even_ab : Even (a + b) := by
            rw [← hsplit] at hpair
            exact hpair.1
          rwa [ha_eq, hb_zero, add_zero] at h_even_ab
        exact (Nat.not_even_iff_odd.mpr hpair.2) h_even_card
      · have h_odd_card : Odd S.card := by
          have h_odd_ab : Odd (a + b) := by
            rw [← hsplit] at hpair
            exact hpair.1
          rwa [ha_eq, hb_zero, add_zero] at h_odd_ab
        exact (Nat.not_odd_iff_even.mpr hpair.2) h_odd_card
    have hb_pos : 0 < b := Nat.pos_of_ne_zero hb_ne_zero
    have hb_real : (0 : ℝ) < b := by
      exact_mod_cast hb_pos
    have ha_real : (a : ℝ) = S.card := by
      exact_mod_cast ha_eq
    have hb_one : (1 : ℝ) ≤ b := by
      exact_mod_cast (Nat.succ_le_of_lt hb_pos)
    linarith

/-- Helper for Theorem 4.46: the box constraints alone give the weak bound with right-hand side
`|S|`. -/
lemma odd_set_inequality_upper_bound_of_mem_box {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) (S : Finset (Fin n)) :
    S.sum x - (Finset.univ \ S).sum x ≤ S.card := by
  rcases hx with ⟨hx0, hx1⟩
  -- Bound the positive part by `|S|` and drop the nonnegative complementary sum.
  have hsum_le : S.sum x ≤ S.card := by
    calc
      S.sum x ≤ S.sum fun _ : Fin n ↦ (1 : ℝ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hx1 i
      _ = S.card := by simp
  have hcomp_nonneg : (0 : ℝ) ≤ (Finset.univ \ S).sum x := by
    exact Finset.sum_nonneg fun i hi ↦ hx0 i
  linarith

/-- Helper for Theorem 4.46: every `0/1` vector lies in the unit box. -/
lemma is_zero_one_vector_mem_box {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    x ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  constructor
  · intro i
    rcases hx i with h0 | h1
    · simp [h0]
    · simp [h1]
  · intro i
    rcases hx i with h0 | h1
    · simp [h0]
    · simp [h1]

/-- Helper for Theorem 4.46: appending a trailing `0` preserves the number of `1`-coordinates. -/
lemma one_coordinate_count_snoc_zero {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    one_coordinate_count (Fin.snoc x 0) = one_coordinate_count x := by
  have hsnoc : is_zero_one_vector (Fin.snoc x 0) := is_zero_one_vector_snoc_zero hx
  -- Compare the count with the total coordinate sum on the `0/1` vectors.
  have hcount_real :
      (one_coordinate_count (Fin.snoc x 0) : ℝ) = (one_coordinate_count x : ℝ) := by
    calc
      (one_coordinate_count (Fin.snoc x 0) : ℝ) = Finset.univ.sum (Fin.snoc x 0) := by
        symm
        simpa [one_coordinate_count] using
          sum_eq_card_filter_of_zero_one (Fin.snoc x 0) Finset.univ hsnoc
      _ = Finset.univ.sum x := by
        rw [Fin.sum_univ_castSucc]
        simp
      _ = (one_coordinate_count x : ℝ) := by
        simpa [one_coordinate_count] using
          sum_eq_card_filter_of_zero_one x Finset.univ hx
  exact_mod_cast hcount_real

/-- Helper for Theorem 4.46: appending a trailing `1` increases the number of `1`-coordinates by
one. -/
lemma one_coordinate_count_snoc_one {n : ℕ} {x : Fin n → ℝ}
    (hx : is_zero_one_vector x) :
    one_coordinate_count (Fin.snoc x 1) = one_coordinate_count x + 1 := by
  have hsnoc : is_zero_one_vector (Fin.snoc x 1) := is_zero_one_vector_snoc_one hx
  -- Compare the count with the total coordinate sum on the `0/1` vectors.
  have hcount_real :
      (one_coordinate_count (Fin.snoc x 1) : ℝ) = (one_coordinate_count x : ℝ) + 1 := by
    calc
      (one_coordinate_count (Fin.snoc x 1) : ℝ) = Finset.univ.sum (Fin.snoc x 1) := by
        symm
        simpa [one_coordinate_count] using
          sum_eq_card_filter_of_zero_one (Fin.snoc x 1) Finset.univ hsnoc
      _ = Finset.univ.sum x + 1 := by
        rw [Fin.sum_univ_castSucc]
        simp
      _ = (one_coordinate_count x : ℝ) + 1 := by
        congr 1
        simpa [one_coordinate_count] using
          sum_eq_card_filter_of_zero_one x Finset.univ hx
  exact_mod_cast hcount_real

/-- Helper for Theorem 4.46: each odd-set inequality defines a convex halfspace. -/
lemma convex_odd_set_halfspace {n : ℕ} (S : Finset (Fin n)) :
    Convex ℝ {x : Fin n → ℝ | odd_set_inequality S x} := by
  let f : (Fin n → ℝ) →ₗ[ℝ] ℝ :=
    (∑ i ∈ S, (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) -
      ∑ i ∈ (Finset.univ \ S), (LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)
  -- The odd-set inequality is the preimage of a real interval under a linear functional.
  have hf :
      {x : Fin n → ℝ | odd_set_inequality S x} = f ⁻¹' Set.Iic ((S.card : ℝ) - 1) := by
    ext x
    simp [odd_set_inequality, f]
  rw [hf]
  exact (convex_Iic _).linear_preimage f

/-- Helper for Theorem 4.46: the right-hand side odd-set system is a convex set. -/
lemma convex_odd_set_polyhedron (n : ℕ) :
    Convex ℝ (odd_set_polyhedron n) := by
  -- The box is convex, and intersecting it with all odd-set halfspaces preserves convexity.
  refine (convex_Icc _ _).inter ?_
  refine convex_iInter fun S ↦ ?_
  exact convex_odd_set_halfspace S.1

/-- Helper for Theorem 4.46: the even-parity companion system is convex for the same reason. -/
lemma convex_even_set_polyhedron (n : ℕ) :
    Convex ℝ (even_set_polyhedron n) := by
  -- The companion polyhedron differs only by the parity of the indexing family.
  refine (convex_Icc _ _).inter ?_
  refine convex_iInter fun S ↦ ?_
  exact convex_odd_set_halfspace S.1

/-- Helper for Theorem 4.46: every even `0/1` vector lies in the odd-set polyhedron. -/
lemma even_zero_one_vectors_subset_odd_set_polyhedron (n : ℕ) :
    even_zero_one_vectors n ⊆ odd_set_polyhedron n := by
  intro x hx
  rcases hx with ⟨hx_zero_one, hx_even⟩
  constructor
  · -- The box constraints are the standard `0/1` coordinate bounds.
    exact is_zero_one_vector_mem_box hx_zero_one
  · -- The odd-set inequalities are the parity counting argument proved above.
    rw [Set.mem_iInter]
    intro S
    exact odd_set_inequality_of_even_zero_one_vector hx_zero_one hx_even S.2

/-- Helper for Theorem 4.46: every odd `0/1` vector lies in the even-parity companion
polyhedron. -/
lemma odd_zero_one_vectors_subset_even_set_polyhedron (n : ℕ) :
    odd_zero_one_vectors n ⊆ even_set_polyhedron n := by
  intro x hx
  rcases hx with ⟨hx_zero_one, hx_odd⟩
  constructor
  · -- The box constraints are again just the coordinatewise `0/1` bounds.
    exact is_zero_one_vector_mem_box hx_zero_one
  · -- The parity-mismatch lemma closes every even-indexed inequality.
    rw [Set.mem_iInter]
    intro S
    exact
      odd_set_inequality_of_zero_one_vector_of_opposite_parity hx_zero_one
        (Or.inr ⟨hx_odd, S.2⟩)

/-- Helper for Theorem 4.46: splitting on the last coordinate swaps the even and odd parity
vertex families exactly as in the source proof. -/
lemma parity_zero_one_vectors_succ_decompose (n : ℕ) :
    (even_zero_one_vectors (n + 1) =
      ((fun x : Fin n → ℝ ↦ Fin.snoc x 0) '' even_zero_one_vectors n) ∪
        ((fun x : Fin n → ℝ ↦ Fin.snoc x 1) '' odd_zero_one_vectors n)) ∧
    (odd_zero_one_vectors (n + 1) =
      ((fun x : Fin n → ℝ ↦ Fin.snoc x 0) '' odd_zero_one_vectors n) ∪
        ((fun x : Fin n → ℝ ↦ Fin.snoc x 1) '' even_zero_one_vectors n)) := by
  constructor
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hy_zero_one, hy_even⟩
      let x : Fin n → ℝ := fun i ↦ y i.castSucc
      have hx_zero_one : is_zero_one_vector x := by
        -- The prefix coordinates inherit the `0/1` property directly from `y`.
        intro i
        simpa [x] using hy_zero_one i.castSucc
      have hy_snoc : Fin.snoc x (y (Fin.last n)) = y := by
        -- Rebuild `y` from its prefix and its last coordinate.
        simpa [x] using snoc_prefix_last y
      rcases hy_zero_one (Fin.last n) with hlast | hlast
      · have hy_zero : Fin.snoc x 0 = y := by
          simpa [hlast] using hy_snoc
        left
        refine ⟨x, ?_, hy_zero⟩
        refine ⟨hx_zero_one, ?_⟩
        -- Appending `0` leaves the parity of the number of `1`-coordinates unchanged.
        have hy_even_zero : Even (one_coordinate_count (Fin.snoc x 0)) := by
          simpa [← hy_zero] using hy_even
        simpa [one_coordinate_count_snoc_zero hx_zero_one] using hy_even_zero
      · have hy_one : Fin.snoc x 1 = y := by
          simpa [hlast] using hy_snoc
        right
        refine ⟨x, ?_, hy_one⟩
        refine ⟨hx_zero_one, ?_⟩
        -- If the last coordinate is `1`, then removing it flips even parity to odd parity.
        have hy_even_one : Even (one_coordinate_count (Fin.snoc x 1)) := by
          simpa [← hy_one] using hy_even
        have hy_even_snoc : Even (one_coordinate_count x + 1) := by
          simpa [one_coordinate_count_snoc_one hx_zero_one] using hy_even_one
        exact Nat.not_even_iff_odd.mp ((Nat.even_add_one).1 hy_even_snoc)
    · intro hy
      rcases hy with hy | hy
      · rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨hx_zero_one, hx_even⟩
        refine ⟨is_zero_one_vector_snoc_zero hx_zero_one, ?_⟩
        -- The `snoc 0` branch preserves even parity.
        simpa [one_coordinate_count_snoc_zero hx_zero_one] using hx_even
      · rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨hx_zero_one, hx_odd⟩
        refine ⟨is_zero_one_vector_snoc_one hx_zero_one, ?_⟩
        -- The `snoc 1` branch turns odd parity into even parity.
        simpa [one_coordinate_count_snoc_one hx_zero_one] using hx_odd.add_one
  · ext y
    constructor
    · intro hy
      rcases hy with ⟨hy_zero_one, hy_odd⟩
      let x : Fin n → ℝ := fun i ↦ y i.castSucc
      have hx_zero_one : is_zero_one_vector x := by
        -- The prefix coordinates again inherit the `0/1` property from `y`.
        intro i
        simpa [x] using hy_zero_one i.castSucc
      have hy_snoc : Fin.snoc x (y (Fin.last n)) = y := by
        -- Rebuild `y` from its prefix and its last coordinate.
        simpa [x] using snoc_prefix_last y
      rcases hy_zero_one (Fin.last n) with hlast | hlast
      · have hy_zero : Fin.snoc x 0 = y := by
          simpa [hlast] using hy_snoc
        left
        refine ⟨x, ?_, hy_zero⟩
        refine ⟨hx_zero_one, ?_⟩
        -- Appending `0` leaves odd parity unchanged.
        have hy_odd_zero : Odd (one_coordinate_count (Fin.snoc x 0)) := by
          simpa [← hy_zero] using hy_odd
        simpa [one_coordinate_count_snoc_zero hx_zero_one] using hy_odd_zero
      · have hy_one : Fin.snoc x 1 = y := by
          simpa [hlast] using hy_snoc
        right
        refine ⟨x, ?_, hy_one⟩
        refine ⟨hx_zero_one, ?_⟩
        -- If the last coordinate is `1`, then removing it flips odd parity to even parity.
        have hy_odd_one : Odd (one_coordinate_count (Fin.snoc x 1)) := by
          simpa [← hy_one] using hy_odd
        have hy_odd_snoc : Odd (one_coordinate_count x + 1) := by
          simpa [one_coordinate_count_snoc_one hx_zero_one] using hy_odd_one
        exact Nat.not_odd_iff_even.mp ((Nat.odd_add_one).1 hy_odd_snoc)
    · intro hy
      rcases hy with hy | hy
      · rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨hx_zero_one, hx_odd⟩
        refine ⟨is_zero_one_vector_snoc_zero hx_zero_one, ?_⟩
        -- The `snoc 0` branch preserves odd parity.
        simpa [one_coordinate_count_snoc_zero hx_zero_one] using hx_odd
      · rcases hy with ⟨x, hx, rfl⟩
        rcases hx with ⟨hx_zero_one, hx_even⟩
        refine ⟨is_zero_one_vector_snoc_one hx_zero_one, ?_⟩
        -- The `snoc 1` branch turns even parity into odd parity.
        simpa [one_coordinate_count_snoc_one hx_zero_one] using hx_even.add_one

/-- Helper for Theorem 4.46: the `snoc 0` branch is a linear map, so convex hulls commute with
its image exactly as required by the source induction. -/
def snocZeroLinear (n : ℕ) : (Fin n → ℝ) →ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fun x ↦ Fin.snoc x 0
  map_add' x y := by
    -- Check additivity on the prefix coordinates and on the appended zero coordinate.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simp
  map_smul' a x := by
    -- Scalar multiplication behaves identically on the prefix and keeps the last coordinate zero.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp
    · simp

/-- Helper for Theorem 4.46: `snocZeroLinear` evaluates to `Fin.snoc x 0`. -/
@[simp] lemma snocZeroLinear_apply {n : ℕ} (x : Fin n → ℝ) :
    snocZeroLinear n x = Fin.snoc x 0 := by
  rfl

/-- Helper for Theorem 4.46: the `snoc 1` branch is affine, so convex hulls commute with its image
without introducing manual translation algebra. -/
def snocOneAffine (n : ℕ) : (Fin n → ℝ) →ᵃ[ℝ] (Fin (n + 1) → ℝ) where
  toFun := fun x ↦ Fin.snoc x 1
  linear := snocZeroLinear n
  map_vadd' p v := by
    -- The affine map shares the same linear part on the prefix coordinates and fixes the last
    -- coordinate at `1`.
    ext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · simp [snocZeroLinear]
    · simp [snocZeroLinear]

/-- Helper for Theorem 4.46: `snocOneAffine` evaluates to `Fin.snoc x 1`. -/
@[simp] lemma snocOneAffine_apply {n : ℕ} (x : Fin n → ℝ) :
    snocOneAffine n x = Fin.snoc x 1 := by
  rfl

/-- Helper for Theorem 4.46: the linear `snoc 0` image of a convex hull is the convex hull of the
corresponding `snoc 0` image. -/
lemma snocZeroLinear_image_convexHull (n : ℕ) (s : Set (Fin n → ℝ)) :
    snocZeroLinear n '' convexHull ℝ s =
      convexHull ℝ ((fun x : Fin n → ℝ ↦ Fin.snoc x 0) '' s) := by
  -- This is the exact linear-image normalization needed for the `snoc 0` induction branch.
  simpa [snocZeroLinear] using (snocZeroLinear n).image_convexHull s

/-- Helper for Theorem 4.46: the affine `snoc 1` image of a convex hull is the convex hull of the
corresponding `snoc 1` image. -/
lemma snocOneAffine_image_convexHull (n : ℕ) (s : Set (Fin n → ℝ)) :
    snocOneAffine n '' convexHull ℝ s =
      convexHull ℝ ((fun x : Fin n → ℝ ↦ Fin.snoc x 1) '' s) := by
  -- This is the affine-image normalization needed for the parity-swapping `snoc 1` branch.
  simpa [snocOneAffine] using (snocOneAffine n).image_convexHull s

/-- Helper for Theorem 4.46: `Fin.snoc` carries a weighted prefix combination to the corresponding
ambient weighted combination of the two boundary slices. -/
lemma snoc_weighted_sum {n : ℕ} (x0 x1 : Fin n → ℝ) (t : ℝ) :
    Fin.snoc ((1 - t) • x0 + t • x1) t =
      (1 - t) • Fin.snoc x0 0 + t • Fin.snoc x1 1 := by
  -- Check the identity on the prefix coordinates and on the new last coordinate separately.
  ext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · -- On prefix coordinates, `Fin.snoc` is just the original weighted sum.
    simp [sub_eq_add_neg]
  · -- On the last coordinate, the boundary slices contribute `0` and `1`.
    simp

/-- Helper for Theorem 4.46: if the two boundary slices are already convex and nonempty, then
membership of `Fin.snoc x t` in the hull of those slices is exactly a weighted prefix
decomposition with weights `1 - t` and `t`. -/
lemma snoc_mem_convexHullSlices_iff {n : ℕ} {A B : Set (Fin n → ℝ)}
    (hA : Convex ℝ A) (hB : Convex ℝ B) (hA_nonempty : A.Nonempty) (hB_nonempty : B.Nonempty)
    {x : Fin n → ℝ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((Fin.snoc x t : Fin (n + 1) → ℝ)) ∈
        convexHull ℝ
          (((fun z : Fin n → ℝ ↦ Fin.snoc z 0) '' A) ∪
            ((fun z : Fin n → ℝ ↦ Fin.snoc z 1) '' B)) ↔
      ∃ x0 ∈ A, ∃ x1 ∈ B, x = (1 - t) • x0 + t • x1 := by
  let s0 : Set (Fin (n + 1) → ℝ) := (fun z : Fin n → ℝ ↦ Fin.snoc z 0) '' A
  let s1 : Set (Fin (n + 1) → ℝ) := (fun z : Fin n → ℝ ↦ Fin.snoc z 1) '' B
  have hs0 : convexHull ℝ s0 = s0 := by
    -- The `snoc 0` image of a convex set is convex, so its hull collapses back to the image.
    calc
      convexHull ℝ s0 = snocZeroLinear n '' convexHull ℝ A := by
        simpa [s0] using (snocZeroLinear_image_convexHull n A).symm
      _ = snocZeroLinear n '' A := by
        rw [hA.convexHull_eq]
      _ = s0 := by
        ext y
        simp [s0, snocZeroLinear_apply]
  have hs1 : convexHull ℝ s1 = s1 := by
    -- The same normalization works for the affine `snoc 1` branch.
    calc
      convexHull ℝ s1 = snocOneAffine n '' convexHull ℝ B := by
        simpa [s1] using (snocOneAffine_image_convexHull n B).symm
      _ = snocOneAffine n '' B := by
        rw [hB.convexHull_eq]
      _ = s1 := by
        ext y
        simp [s1, snocOneAffine_apply]
  constructor
  · intro hx
    have hs0_nonempty : s0.Nonempty := by
      simpa [s0] using
        hA_nonempty.image (fun z : Fin n → ℝ ↦ (Fin.snoc z (0 : ℝ) : Fin (n + 1) → ℝ))
    have hs1_nonempty : s1.Nonempty := by
      simpa [s1] using
        hB_nonempty.image (fun z : Fin n → ℝ ↦ (Fin.snoc z (1 : ℝ) : Fin (n + 1) → ℝ))
    have hxJoin : Fin.snoc x t ∈ convexJoin ℝ s0 s1 := by
      -- Rewrite the hull of the union to the convex join of the two already-convex branches.
      rw [convexHull_union hs0_nonempty hs1_nonempty, hs0, hs1] at hx
      exact hx
    rw [mem_convexJoin] at hxJoin
    rcases hxJoin with ⟨y0, ⟨x0, hx0, rfl⟩, y1, ⟨x1, hx1, rfl⟩, hseg⟩
    rw [segment_eq_image_lineMap] at hseg
    rcases hseg with ⟨θ, hθ_mem, hline⟩
    have hθ : θ = t := by
      -- Reading the last coordinate pins down the segment parameter uniquely.
      have hlast := congrArg (fun y : Fin (n + 1) → ℝ ↦ y (Fin.last n)) hline
      simp [AffineMap.lineMap_apply_module] at hlast
      simpa using hlast
    refine ⟨x0, hx0, x1, hx1, ?_⟩
    ext i
    -- Once the segment parameter is identified with `t`, the prefix coordinates give the
    -- weighted decomposition of `x`.
    have hi := congrArg (fun y : Fin (n + 1) → ℝ ↦ y i.castSucc) hline
    simpa [AffineMap.lineMap_apply_module, hθ, Pi.smul_apply, smul_eq_mul] using hi.symm
  · rintro ⟨x0, hx0, x1, hx1, rfl⟩
    have hseg :
        Fin.snoc ((1 - t) • x0 + t • x1) t ∈ segment ℝ (Fin.snoc x0 0) (Fin.snoc x1 1) := by
      -- The ambient weighted sum is the segment point with coefficients `1 - t` and `t`.
      refine ⟨1 - t, t, by linarith, ht0, by linarith, ?_⟩
      simpa using (snoc_weighted_sum x0 x1 t).symm
    have hxJoin :
        Fin.snoc ((1 - t) • x0 + t • x1) t ∈ convexJoin ℝ s0 s1 := by
      -- The two endpoint witnesses put the whole segment inside the join of the boundary slices.
      rw [mem_convexJoin]
      exact ⟨Fin.snoc x0 0, ⟨x0, hx0, rfl⟩, Fin.snoc x1 1, ⟨x1, hx1, rfl⟩, hseg⟩
    -- The convex join sits inside the hull of the union of the two boundary slices.
    exact (convexJoin_subset_convexHull s0 s1) hxJoin

/-- Helper for Theorem 4.46: appending a trailing `0` preserves membership in the unit box. -/
lemma snoc_zero_mem_box_iff {n : ℕ} {x : Fin n → ℝ} :
    Fin.snoc x 0 ∈ Set.Icc (0 : Fin (n + 1) → ℝ) 1 ↔ x ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  constructor
  · intro hx
    -- Restrict the pointwise bounds on the `snoc` tuple to the prefix coordinates.
    constructor
    · intro i
      simpa using hx.1 i.castSucc
    · intro i
      simpa using hx.2 i.castSucc
  · intro hx
    -- Rebuild the pointwise bounds on the `snoc` tuple from the prefix bounds and the last
    -- coordinate value `0`.
    constructor
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using hx.1 j
      · simp
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using hx.2 j
      · simp

/-- Helper for Theorem 4.46: appending a trailing `1` preserves membership in the unit box. -/
lemma snoc_one_mem_box_iff {n : ℕ} {x : Fin n → ℝ} :
    Fin.snoc x 1 ∈ Set.Icc (0 : Fin (n + 1) → ℝ) 1 ↔ x ∈ Set.Icc (0 : Fin n → ℝ) 1 := by
  constructor
  · intro hx
    -- Restrict the pointwise bounds on the `snoc` tuple to the prefix coordinates.
    constructor
    · intro i
      simpa using hx.1 i.castSucc
    · intro i
      simpa using hx.2 i.castSucc
  · intro hx
    -- Rebuild the pointwise bounds on the `snoc` tuple from the prefix bounds and the last
    -- coordinate value `1`.
    constructor
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using hx.1 j
      · simp
    · intro i
      rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
      · simpa using hx.2 j
      · simp

/-- Helper for Theorem 4.46: if the last index is absent, the prefix reconstruction preserves
cardinality. -/
lemma prefixFinset_card_of_last_not_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (hlast : Fin.last n ∉ T) :
    (prefixFinset T).card = T.card := by
  -- Count cards after reconstructing `T` from its prefix part.
  have hsplit : castSuccFinset (prefixFinset T) = T := (prefixFinset_last_split T).1 hlast
  calc
    (prefixFinset T).card = (castSuccFinset (prefixFinset T)).card := by
      symm
      simpa using card_castSuccFinset (prefixFinset T)
    _ = T.card := by simp [hsplit]

/-- Helper for Theorem 4.46: if the last index is present, the ambient set has one more element
than its prefix part. -/
lemma card_eq_prefixFinset_card_add_one_of_last_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (hlast : Fin.last n ∈ T) :
    T.card = (prefixFinset T).card + 1 := by
  -- Count cards after reconstructing `T` by reinserting the last index into its prefix part.
  have hsplit :
      insert (Fin.last n) (castSuccFinset (prefixFinset T)) = T :=
    (prefixFinset_last_split T).2 hlast
  calc
    T.card = (insert (Fin.last n) (castSuccFinset (prefixFinset T))).card := by
      simp [hsplit]
    _ = (castSuccFinset (prefixFinset T)).card + 1 := by
      simp [last_not_mem_castSuccFinset]
    _ = (prefixFinset T).card + 1 := by
      simp [card_castSuccFinset]

/-- Helper for Theorem 4.46: an odd ambient set without the last index has odd prefix
cardinality. -/
lemma odd_prefixFinset_card_of_odd_last_not_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (hodd : Odd T.card) (hlast : Fin.last n ∉ T) :
    Odd (prefixFinset T).card := by
  -- The absent-last case does not change cardinality.
  simpa [prefixFinset_card_of_last_not_mem hlast] using hodd

/-- Helper for Theorem 4.46: an odd ambient set with the last index has even prefix cardinality. -/
lemma even_prefixFinset_card_of_odd_last_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (hodd : Odd T.card) (hlast : Fin.last n ∈ T) :
    Even (prefixFinset T).card := by
  -- Removing the distinguished last element flips odd cardinality to even cardinality.
  have hodd' : Odd ((prefixFinset T).card + 1) := by
    simpa [card_eq_prefixFinset_card_add_one_of_last_mem hlast] using hodd
  exact Nat.not_odd_iff_even.mp ((Nat.odd_add_one).1 hodd')

/-- Helper for Theorem 4.46: an even ambient set without the last index has even prefix
cardinality. -/
lemma even_prefixFinset_card_of_even_last_not_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (heven : Even T.card) (hlast : Fin.last n ∉ T) :
    Even (prefixFinset T).card := by
  -- The absent-last case does not change cardinality.
  simpa [prefixFinset_card_of_last_not_mem hlast] using heven

/-- Helper for Theorem 4.46: an even ambient set with the last index has odd prefix cardinality. -/
lemma odd_prefixFinset_card_of_even_last_mem {n : ℕ} {T : Finset (Fin (n + 1))}
    (heven : Even T.card) (hlast : Fin.last n ∈ T) :
    Odd (prefixFinset T).card := by
  -- Removing the distinguished last element flips even cardinality to odd cardinality.
  have heven' : Even ((prefixFinset T).card + 1) := by
    simpa [card_eq_prefixFinset_card_add_one_of_last_mem hlast] using heven
  exact Nat.not_even_iff_odd.mp ((Nat.even_add_one).1 heven')

/-- Helper for Theorem 4.46: deleting the last index from the complement leaves only the prefix
complement contribution. -/
lemma sum_compl_insert_last_castSuccFinset_snoc {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) (r : ℝ) :
    (Finset.univ \ insert (Fin.last n) (castSuccFinset S)).sum (Fin.snoc x r) =
      (Finset.univ \ S).sum x := by
  -- Compare the partition of `Fin (n + 1)` into the inserted set and its complement with the
  -- corresponding partition of the prefix coordinates.
  have hpartition :
      (Finset.univ \ insert (Fin.last n) (castSuccFinset S)).sum (Fin.snoc x r) +
          (insert (Fin.last n) (castSuccFinset S)).sum (Fin.snoc x r) =
        Finset.univ.sum (Fin.snoc x r) := by
    exact Finset.sum_sdiff (Finset.subset_univ _)
  have hinsert :
      (insert (Fin.last n) (castSuccFinset S)).sum (Fin.snoc x r) = S.sum x + r := by
    rw [Finset.sum_insert (last_not_mem_castSuccFinset S), sum_castSuccFinset_snoc]
    simp [add_comm]
  have hprefix :
      (Finset.univ \ S).sum x + S.sum x = Finset.univ.sum x := by
    exact Finset.sum_sdiff (Finset.subset_univ S)
  have hpartition' :
      (Finset.univ \ insert (Fin.last n) (castSuccFinset S)).sum (Fin.snoc x r) +
          (S.sum x + r) =
        Finset.univ.sum x + r := by
    have hpartition'' := hpartition
    rw [hinsert, Fin.sum_univ_castSucc] at hpartition''
    simpa [add_comm, add_left_comm, add_assoc] using hpartition''
  linarith

/-- Helper for Theorem 4.46: the normalized odd last-coordinate slice on the prefix variables. -/
def odd_prefix_slice (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      (∀ S : Finset (Fin n), Odd S.card →
        S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - 1 + t) ∧
      (∀ S : Finset (Fin n), Even S.card →
        S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - t)}

/-- Helper for Theorem 4.46: the normalized even last-coordinate slice on the prefix variables. -/
def even_prefix_slice (n : ℕ) (t : ℝ) : Set (Fin n → ℝ) :=
  {x | x ∈ Set.Icc (0 : Fin n → ℝ) 1 ∧
      (∀ S : Finset (Fin n), Odd S.card →
        S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - t) ∧
      (∀ S : Finset (Fin n), Even S.card →
        S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - 1 + t)}

/-- Helper for Theorem 4.46: the odd-set inequality on `Fin.snoc x t` rewrites to the exact
shifted prefix inequalities used by the source last-coordinate split. -/
lemma odd_set_inequality_snoc_t_rewrites {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) (t : ℝ) :
    (odd_set_inequality (castSuccFinset S) (Fin.snoc x t) ↔
      S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - 1 + t) ∧
    (odd_set_inequality (insert (Fin.last n) (castSuccFinset S)) (Fin.snoc x t) ↔
      S.sum x - (Finset.univ \ S).sum x ≤ (S.card : ℝ) - t) := by
  constructor
  · -- Rewrite the absent-last case to the prefix sum/complement identity and isolate the `t` term.
    unfold odd_set_inequality
    rw [sum_castSuccFinset_snoc, sum_compl_castSuccFinset_snoc, card_castSuccFinset]
    constructor <;> intro h <;> linarith
  · -- Rewrite the present-last case similarly, with the last coordinate contributing through the
    -- inserted set instead of the complement.
    unfold odd_set_inequality
    rw [Finset.sum_insert (last_not_mem_castSuccFinset S), sum_castSuccFinset_snoc,
      sum_compl_insert_last_castSuccFinset_snoc, Finset.card_insert_of_notMem,
      card_castSuccFinset]
    · simp only [Fin.snoc_last, Nat.cast_add, Nat.cast_one]
      constructor <;> intro h <;> linarith
    · exact last_not_mem_castSuccFinset S

/-- Helper for Theorem 4.46: membership of `Fin.snoc x t` in the odd/even parity polyhedra is
equivalent to the fixed-`t` source slice conditions on the prefix coordinates. -/
lemma snoc_mem_parity_polyhedron_iff_prefix_slice {n : ℕ} (x : Fin n → ℝ) (t : ℝ) :
    (Fin.snoc x t ∈ odd_set_polyhedron (n + 1) ↔
      0 ≤ t ∧ t ≤ 1 ∧ x ∈ odd_prefix_slice n t) ∧
    (Fin.snoc x t ∈ even_set_polyhedron (n + 1) ↔
      0 ≤ t ∧ t ≤ 1 ∧ x ∈ even_prefix_slice n t) := by
  constructor
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      have ht0 : 0 ≤ t := by
        simpa using hbox.1 (Fin.last n)
      have ht1 : t ≤ 1 := by
        simpa using hbox.2 (Fin.last n)
      refine ⟨ht0, ht1, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · -- Restrict the ambient box constraints to the prefix coordinates.
        constructor
        · intro i
          simpa using hbox.1 i.castSucc
        · intro i
          simpa using hbox.2 i.castSucc
      · -- The odd-indexed ambient inequalities without the last coordinate give the odd-prefix
        -- slice bounds.
        intro S hSodd
        have hcastOdd : Odd (castSuccFinset S).card := by
          simpa [card_castSuccFinset] using hSodd
        have hcast :
            odd_set_inequality (castSuccFinset S) (Fin.snoc x t) := by
          exact (Set.mem_iInter.mp hineq) ⟨castSuccFinset S, hcastOdd⟩
        exact (odd_set_inequality_snoc_t_rewrites S x t).1.mp hcast
      · -- The odd ambient inequalities using the last coordinate become the even-prefix bounds.
        intro S hSeven
        have hinsertOdd : Odd (insert (Fin.last n) (castSuccFinset S)).card := by
          simpa [Finset.card_insert_of_notMem, card_castSuccFinset,
            last_not_mem_castSuccFinset] using hSeven.add_one
        have hinsert :
            odd_set_inequality (insert (Fin.last n) (castSuccFinset S)) (Fin.snoc x t) := by
          exact (Set.mem_iInter.mp hineq) ⟨insert (Fin.last n) (castSuccFinset S), hinsertOdd⟩
        exact (odd_set_inequality_snoc_t_rewrites S x t).2.mp hinsert
    · rintro ⟨ht0, ht1, hxslice⟩
      refine ⟨?_, ?_⟩
      · -- Rebuild the ambient box from the prefix box and the explicit last-coordinate bounds.
        rcases hxslice with ⟨hbox, -, -⟩
        constructor
        · intro i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simpa using hbox.1 j
          · simpa using ht0
        · intro i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simpa using hbox.2 j
          · simpa using ht1
      · -- Route correction: the ambient odd-system is now discharged by splitting the odd index
        -- set according to whether it uses the last coordinate and then applying the normalized
        -- prefix-slice bounds.
        rw [Set.mem_iInter]
        intro T
        rcases hxslice with ⟨-, hoddSlice, hevenSlice⟩
        by_cases hlast : Fin.last n ∈ T.1
        · have hsplit :
              insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
            (prefixFinset_last_split T.1).2 hlast
          have hprefixEven : Even (prefixFinset T.1).card :=
            even_prefixFinset_card_of_odd_last_mem T.2 hlast
          have hprefix :
              (prefixFinset T.1).sum x - (Finset.univ \ prefixFinset T.1).sum x ≤
                ((prefixFinset T.1).card : ℝ) - t :=
            hevenSlice (prefixFinset T.1) hprefixEven
          rw [← hsplit]
          exact (odd_set_inequality_snoc_t_rewrites (prefixFinset T.1) x t).2.mpr hprefix
        · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
            (prefixFinset_last_split T.1).1 hlast
          have hprefixOdd : Odd (prefixFinset T.1).card :=
            odd_prefixFinset_card_of_odd_last_not_mem T.2 hlast
          have hprefix :
              (prefixFinset T.1).sum x - (Finset.univ \ prefixFinset T.1).sum x ≤
                ((prefixFinset T.1).card : ℝ) - 1 + t :=
            hoddSlice (prefixFinset T.1) hprefixOdd
          rw [← hsplit]
          exact (odd_set_inequality_snoc_t_rewrites (prefixFinset T.1) x t).1.mpr hprefix
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      have ht0 : 0 ≤ t := by
        simpa using hbox.1 (Fin.last n)
      have ht1 : t ≤ 1 := by
        simpa using hbox.2 (Fin.last n)
      refine ⟨ht0, ht1, ?_⟩
      refine ⟨?_, ?_, ?_⟩
      · -- Restrict the ambient box constraints to the prefix coordinates.
        constructor
        · intro i
          simpa using hbox.1 i.castSucc
        · intro i
          simpa using hbox.2 i.castSucc
      · -- For the even ambient polyhedron, odd prefix sets arise from odd ambient sets using the
        -- last coordinate.
        intro S hSodd
        have hinsertEven : Even (insert (Fin.last n) (castSuccFinset S)).card := by
          simpa [Finset.card_insert_of_notMem, card_castSuccFinset,
            last_not_mem_castSuccFinset] using hSodd.add_one
        have hinsert :
            odd_set_inequality (insert (Fin.last n) (castSuccFinset S)) (Fin.snoc x t) := by
          exact (Set.mem_iInter.mp hineq) ⟨insert (Fin.last n) (castSuccFinset S), hinsertEven⟩
        exact (odd_set_inequality_snoc_t_rewrites S x t).2.mp hinsert
      · -- Even prefix sets come from even ambient sets that avoid the last coordinate.
        intro S hSeven
        have hcastEven : Even (castSuccFinset S).card := by
          simpa [card_castSuccFinset] using hSeven
        have hcast :
            odd_set_inequality (castSuccFinset S) (Fin.snoc x t) := by
          exact (Set.mem_iInter.mp hineq) ⟨castSuccFinset S, hcastEven⟩
        exact (odd_set_inequality_snoc_t_rewrites S x t).1.mp hcast
    · rintro ⟨ht0, ht1, hxslice⟩
      refine ⟨?_, ?_⟩
      · -- Rebuild the ambient box from the prefix box and the explicit last-coordinate bounds.
        rcases hxslice with ⟨hbox, -, -⟩
        constructor
        · intro i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simpa using hbox.1 j
          · simpa using ht0
        · intro i
          rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
          · simpa using hbox.2 j
          · simpa using ht1
      · -- The same last-coordinate split now uses the even ambient indexing family.
        rw [Set.mem_iInter]
        intro T
        rcases hxslice with ⟨-, hoddSlice, hevenSlice⟩
        by_cases hlast : Fin.last n ∈ T.1
        · have hsplit :
              insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
            (prefixFinset_last_split T.1).2 hlast
          have hprefixOdd : Odd (prefixFinset T.1).card :=
            odd_prefixFinset_card_of_even_last_mem T.2 hlast
          have hprefix :
              (prefixFinset T.1).sum x - (Finset.univ \ prefixFinset T.1).sum x ≤
                ((prefixFinset T.1).card : ℝ) - t :=
            hoddSlice (prefixFinset T.1) hprefixOdd
          rw [← hsplit]
          exact (odd_set_inequality_snoc_t_rewrites (prefixFinset T.1) x t).2.mpr hprefix
        · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
            (prefixFinset_last_split T.1).1 hlast
          have hprefixEven : Even (prefixFinset T.1).card :=
            even_prefixFinset_card_of_even_last_not_mem T.2 hlast
          have hprefix :
              (prefixFinset T.1).sum x - (Finset.univ \ prefixFinset T.1).sum x ≤
                ((prefixFinset T.1).card : ℝ) - 1 + t :=
            hevenSlice (prefixFinset T.1) hprefixEven
          rw [← hsplit]
          exact (odd_set_inequality_snoc_t_rewrites (prefixFinset T.1) x t).1.mpr hprefix

/-- Helper for Theorem 4.46: on the exact `snoc 0` boundary slice, the odd-set inequality indexed
by a `castSucc` subset is exactly the prefix inequality. -/
lemma odd_set_inequality_castSuccFinset_snoc_zero_iff {n : ℕ} (S : Finset (Fin n))
    (x : Fin n → ℝ) :
    odd_set_inequality (castSuccFinset S) (Fin.snoc x 0) ↔ odd_set_inequality S x := by
  -- Rewrite the lifted sums and cardinalities back to their prefix forms.
  unfold odd_set_inequality
  rw [sum_castSuccFinset_snoc, sum_compl_castSuccFinset_snoc, card_castSuccFinset]
  simp

/-- Helper for Theorem 4.46: on the exact `snoc 1` boundary slice, the odd-set inequality indexed
by an inserted-last subset is exactly the prefix inequality. -/
lemma odd_set_inequality_insert_last_castSuccFinset_snoc_one_iff {n : ℕ}
    (S : Finset (Fin n)) (x : Fin n → ℝ) :
    odd_set_inequality (insert (Fin.last n) (castSuccFinset S)) (Fin.snoc x 1) ↔
      odd_set_inequality S x := by
  -- Rewrite the lifted sums and cardinalities, then cancel the common `+ 1` contribution from the
  -- last coordinate.
  unfold odd_set_inequality
  rw [Finset.sum_insert (last_not_mem_castSuccFinset S), sum_castSuccFinset_snoc,
    sum_compl_insert_last_castSuccFinset_snoc, Finset.card_insert_of_notMem,
    card_castSuccFinset]
  · simp only [Fin.snoc_last, Nat.cast_add, Nat.cast_one]
    constructor <;> intro h <;> linarith
  · exact last_not_mem_castSuccFinset S

/-- Helper for Theorem 4.46: when the last index belongs to the odd subset and the last coordinate
is `0`, the remaining inequality is the box upper bound on the prefix part. -/
lemma odd_set_inequality_insert_last_castSuccFinset_snoc_zero_of_mem_box {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) (S : Finset (Fin n)) :
    odd_set_inequality (insert (Fin.last n) (castSuccFinset S)) (Fin.snoc x 0) := by
  -- After rewriting the lifted inequality, only the weak bound `≤ |S|` remains.
  unfold odd_set_inequality
  rw [Finset.sum_insert (last_not_mem_castSuccFinset S), sum_castSuccFinset_snoc,
    sum_compl_insert_last_castSuccFinset_snoc, Finset.card_insert_of_notMem,
    card_castSuccFinset]
  · simpa using odd_set_inequality_upper_bound_of_mem_box hx S
  · exact last_not_mem_castSuccFinset S

/-- Helper for Theorem 4.46: when the last index is absent and the last coordinate is `1`, the
remaining inequality is again the box upper bound on the prefix part. -/
lemma odd_set_inequality_castSuccFinset_snoc_one_of_mem_box {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) (S : Finset (Fin n)) :
    odd_set_inequality (castSuccFinset S) (Fin.snoc x 1) := by
  -- After rewriting the lifted inequality, the extra `1` on the right is absorbed by the weak
  -- bound coming from the unit box.
  unfold odd_set_inequality
  rw [sum_castSuccFinset_snoc, sum_compl_castSuccFinset_snoc, card_castSuccFinset]
  have hbound : S.sum x - (Finset.univ \ S).sum x ≤ S.card := by
    simpa using odd_set_inequality_upper_bound_of_mem_box hx S
  linarith

/-- Helper for Theorem 4.46: the odd polyhedron splits into the `snoc 0` odd slice and the
`snoc 1` even slice exactly as in the source proof. -/
lemma odd_set_polyhedron_snoc_slices {n : ℕ} {x : Fin n → ℝ} :
    (Fin.snoc x 0 ∈ odd_set_polyhedron (n + 1) ↔ x ∈ odd_set_polyhedron n) ∧
      (Fin.snoc x 1 ∈ odd_set_polyhedron (n + 1) ↔ x ∈ even_set_polyhedron n) := by
  constructor
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_zero_mem_box_iff).1 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro S
      -- Test the odd inequality on the exact `castSucc` lift of the prefix subset.
      have hcast :
          odd_set_inequality (castSuccFinset S.1) (Fin.snoc x 0) := by
        have hcastOdd : Odd (castSuccFinset S.1).card := by
          simpa [card_castSuccFinset] using S.2
        exact (Set.mem_iInter.mp hineq) ⟨castSuccFinset S.1, hcastOdd⟩
      exact (odd_set_inequality_castSuccFinset_snoc_zero_iff S.1 x).1 hcast
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_zero_mem_box_iff).2 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro T
      -- Split on whether the odd indexing set uses the last coordinate.
      by_cases hlast : Fin.last n ∈ T.1
      · have hsplit :
            insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
          (prefixFinset_last_split T.1).2 hlast
        rw [← hsplit]
        exact odd_set_inequality_insert_last_castSuccFinset_snoc_zero_of_mem_box hbox
          (prefixFinset T.1)
      · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
          (prefixFinset_last_split T.1).1 hlast
        have hprefixOdd : Odd (prefixFinset T.1).card :=
          odd_prefixFinset_card_of_odd_last_not_mem T.2 hlast
        have hprefix :
            odd_set_inequality (prefixFinset T.1) x := by
          exact (Set.mem_iInter.mp hineq) ⟨prefixFinset T.1, hprefixOdd⟩
        rw [← hsplit]
        exact (odd_set_inequality_castSuccFinset_snoc_zero_iff (prefixFinset T.1) x).2 hprefix
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_one_mem_box_iff).1 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro S
      -- Test the odd inequality on the exact inserted-last lift of the prefix subset.
      have hinsertOdd :
          Odd (insert (Fin.last n) (castSuccFinset S.1)).card := by
        simpa [Finset.card_insert_of_notMem, card_castSuccFinset,
          last_not_mem_castSuccFinset] using S.2.add_one
      have hinsert :
          odd_set_inequality (insert (Fin.last n) (castSuccFinset S.1)) (Fin.snoc x 1) := by
        exact (Set.mem_iInter.mp hineq) ⟨insert (Fin.last n) (castSuccFinset S.1), hinsertOdd⟩
      exact (odd_set_inequality_insert_last_castSuccFinset_snoc_one_iff S.1 x).1 hinsert
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_one_mem_box_iff).2 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro T
      -- Split on whether the odd indexing set uses the last coordinate.
      by_cases hlast : Fin.last n ∈ T.1
      · have hsplit :
            insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
          (prefixFinset_last_split T.1).2 hlast
        have hprefixEven : Even (prefixFinset T.1).card :=
          even_prefixFinset_card_of_odd_last_mem T.2 hlast
        have hprefix :
            odd_set_inequality (prefixFinset T.1) x := by
          exact (Set.mem_iInter.mp hineq) ⟨prefixFinset T.1, hprefixEven⟩
        rw [← hsplit]
        exact
          (odd_set_inequality_insert_last_castSuccFinset_snoc_one_iff (prefixFinset T.1) x).2
            hprefix
      · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
          (prefixFinset_last_split T.1).1 hlast
        rw [← hsplit]
        exact odd_set_inequality_castSuccFinset_snoc_one_of_mem_box hbox (prefixFinset T.1)

/-- Helper for Theorem 4.46: the even polyhedron splits into the `snoc 0` even slice and the
`snoc 1` odd slice exactly as in the source proof. -/
lemma even_set_polyhedron_snoc_slices {n : ℕ} {x : Fin n → ℝ} :
    (Fin.snoc x 0 ∈ even_set_polyhedron (n + 1) ↔ x ∈ even_set_polyhedron n) ∧
      (Fin.snoc x 1 ∈ even_set_polyhedron (n + 1) ↔ x ∈ odd_set_polyhedron n) := by
  constructor
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_zero_mem_box_iff).1 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro S
      -- Test the even-indexed inequality on the exact `castSucc` lift of the prefix subset.
      have hcast :
          odd_set_inequality (castSuccFinset S.1) (Fin.snoc x 0) := by
        have hcastEven : Even (castSuccFinset S.1).card := by
          simpa [card_castSuccFinset] using S.2
        exact (Set.mem_iInter.mp hineq) ⟨castSuccFinset S.1, hcastEven⟩
      exact (odd_set_inequality_castSuccFinset_snoc_zero_iff S.1 x).1 hcast
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_zero_mem_box_iff).2 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro T
      -- Split on whether the even indexing set uses the last coordinate.
      by_cases hlast : Fin.last n ∈ T.1
      · have hsplit :
            insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
          (prefixFinset_last_split T.1).2 hlast
        rw [← hsplit]
        exact odd_set_inequality_insert_last_castSuccFinset_snoc_zero_of_mem_box hbox
          (prefixFinset T.1)
      · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
          (prefixFinset_last_split T.1).1 hlast
        have hprefixEven : Even (prefixFinset T.1).card :=
          even_prefixFinset_card_of_even_last_not_mem T.2 hlast
        have hprefix :
            odd_set_inequality (prefixFinset T.1) x := by
          exact (Set.mem_iInter.mp hineq) ⟨prefixFinset T.1, hprefixEven⟩
        rw [← hsplit]
        exact (odd_set_inequality_castSuccFinset_snoc_zero_iff (prefixFinset T.1) x).2 hprefix
  · constructor
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_one_mem_box_iff).1 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro S
      -- Test the even-indexed inequality on the exact inserted-last lift of the prefix subset.
      have hinsertEven :
          Even (insert (Fin.last n) (castSuccFinset S.1)).card := by
        simpa [Finset.card_insert_of_notMem, card_castSuccFinset,
          last_not_mem_castSuccFinset] using S.2.add_one
      have hinsert :
          odd_set_inequality (insert (Fin.last n) (castSuccFinset S.1)) (Fin.snoc x 1) := by
        exact (Set.mem_iInter.mp hineq) ⟨insert (Fin.last n) (castSuccFinset S.1), hinsertEven⟩
      exact (odd_set_inequality_insert_last_castSuccFinset_snoc_one_iff S.1 x).1 hinsert
    · intro hx
      rcases hx with ⟨hbox, hineq⟩
      refine ⟨(snoc_one_mem_box_iff).2 hbox, ?_⟩
      rw [Set.mem_iInter]
      intro T
      -- Split on whether the even indexing set uses the last coordinate.
      by_cases hlast : Fin.last n ∈ T.1
      · have hsplit :
            insert (Fin.last n) (castSuccFinset (prefixFinset T.1)) = T.1 :=
          (prefixFinset_last_split T.1).2 hlast
        have hprefixOdd : Odd (prefixFinset T.1).card :=
          odd_prefixFinset_card_of_even_last_mem T.2 hlast
        have hprefix :
            odd_set_inequality (prefixFinset T.1) x := by
          exact (Set.mem_iInter.mp hineq) ⟨prefixFinset T.1, hprefixOdd⟩
        rw [← hsplit]
        exact
          (odd_set_inequality_insert_last_castSuccFinset_snoc_one_iff (prefixFinset T.1) x).2
            hprefix
      · have hsplit : castSuccFinset (prefixFinset T.1) = T.1 :=
          (prefixFinset_last_split T.1).1 hlast
        rw [← hsplit]
        exact odd_set_inequality_castSuccFinset_snoc_one_of_mem_box hbox (prefixFinset T.1)

/-- Helper for Theorem 4.46: the two odd/even boundary slices already lie in the ambient odd
polyhedron, so their convex hull is contained in that polyhedron. -/
lemma odd_set_polyhedron_contains_convexHull_snoc_slices (n : ℕ) :
    convexHull ℝ
        (((fun x : Fin n → ℝ ↦ Fin.snoc x 0) '' odd_set_polyhedron n) ∪
          ((fun x : Fin n → ℝ ↦ Fin.snoc x 1) '' even_set_polyhedron n)) ⊆
      odd_set_polyhedron (n + 1) := by
  -- The slice equivalences identify each boundary branch with a subset of the target polyhedron,
  -- and convexity then closes the hull containment.
  refine convexHull_min ?_ (convex_odd_set_polyhedron (n + 1))
  rintro y (hy | hy)
  · rcases hy with ⟨x, hx, rfl⟩
    exact (odd_set_polyhedron_snoc_slices (x := x)).1.2 hx
  · rcases hy with ⟨x, hx, rfl⟩
    exact (odd_set_polyhedron_snoc_slices (x := x)).2.2 hx

/-- Helper for Theorem 4.46: the two even/odd boundary slices already lie in the ambient even
polyhedron, so their convex hull is contained in that companion polyhedron. -/
lemma even_set_polyhedron_contains_convexHull_snoc_slices (n : ℕ) :
    convexHull ℝ
        (((fun x : Fin n → ℝ ↦ Fin.snoc x 0) '' even_set_polyhedron n) ∪
          ((fun x : Fin n → ℝ ↦ Fin.snoc x 1) '' odd_set_polyhedron n)) ⊆
      even_set_polyhedron (n + 1) := by
  -- This is the even-parity companion of the previous hull-containment statement.
  refine convexHull_min ?_ (convex_even_set_polyhedron (n + 1))
  rintro y (hy | hy)
  · rcases hy with ⟨x, hx, rfl⟩
    exact (even_set_polyhedron_snoc_slices (x := x)).1.2 hx
  · rcases hy with ⟨x, hx, rfl⟩
    exact (even_set_polyhedron_snoc_slices (x := x)).2.2 hx

/-- Helper for Theorem 4.46: finite sums distribute over the weighted prefix combinations used in
the fixed-slice decomposition. -/
lemma sum_weighted_prefix_combination {n : ℕ} (S : Finset (Fin n))
    (x0 x1 : Fin n → ℝ) (t : ℝ) :
    S.sum ((1 - t) • x0 + t • x1) = (1 - t) * S.sum x0 + t * S.sum x1 := by
  -- Expand the pointwise weighted sum and distribute the finite sum over the two branches.
  simp [Finset.sum_add_distrib, Finset.mul_sum]

/-- Helper for Theorem 4.46: the odd-set left-hand side of a weighted prefix combination splits
into the corresponding weighted odd-set left-hand sides. -/
lemma odd_set_left_side_weighted_combination {n : ℕ} (S : Finset (Fin n))
    (x0 x1 : Fin n → ℝ) (t : ℝ) :
    S.sum ((1 - t) • x0 + t • x1) - (Finset.univ \ S).sum ((1 - t) • x0 + t • x1) =
      (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) +
        t * (S.sum x1 - (Finset.univ \ S).sum x1) := by
  -- Rewrite both sums through the same weighted-sum formula, then collect the two row terms.
  rw [sum_weighted_prefix_combination, sum_weighted_prefix_combination]
  ring

/-- Helper for Theorem 4.46: every weighted combination of an odd-polyhedron point and an
even-polyhedron point satisfies the normalized odd fixed-slice system. -/
lemma weighted_combination_subset_odd_prefix_slice (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    {x | ∃ x0 ∈ odd_set_polyhedron n, ∃ x1 ∈ even_set_polyhedron n,
      x = (1 - t) • x0 + t • x1} ⊆ odd_prefix_slice n t := by
  intro x hx
  rcases hx with ⟨x0, hx0, x1, hx1, rfl⟩
  rcases hx0 with ⟨hx0_box, hx0_ineq⟩
  rcases hx1 with ⟨hx1_box, hx1_ineq⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The unit box is convex, so it contains the weighted combination of the two endpoint
    -- witnesses.
    constructor
    · intro i
      have hx0i : 0 ≤ x0 i := hx0_box.1 i
      have hx1i : 0 ≤ x1 i := hx1_box.1 i
      have h_one_sub : 0 ≤ 1 - t := by linarith
      have h0 : 0 ≤ (1 - t) * x0 i := mul_nonneg h_one_sub hx0i
      have h1 : 0 ≤ t * x1 i := mul_nonneg ht0 hx1i
      simpa [Pi.smul_apply] using add_nonneg h0 h1
    · intro i
      have hx0i : x0 i ≤ 1 := hx0_box.2 i
      have hx1i : x1 i ≤ 1 := hx1_box.2 i
      have h_one_sub : 0 ≤ 1 - t := by linarith
      have h0 : (1 - t) * x0 i ≤ 1 - t := by
        simpa using mul_le_mul_of_nonneg_left hx0i h_one_sub
      have h1 : t * x1 i ≤ t := by
        simpa using mul_le_mul_of_nonneg_left hx1i ht0
      have hsum : (1 - t) * x0 i + t * x1 i ≤ (1 - t) + t := add_le_add h0 h1
      simpa [Pi.smul_apply] using hsum.trans_eq (by ring)
  · intro S hSodd
    -- On odd subsets, the odd endpoint contributes the sharp bound and the even endpoint
    -- contributes only the weak box bound.
    have h0 :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx0_ineq) ⟨S, hSodd⟩
    have h1 :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx1_box S
    have h0_scaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤ (1 - t) * ((S.card : ℝ) - 1) := by
      have h_one_sub : 0 ≤ 1 - t := by linarith
      exact mul_le_mul_of_nonneg_left h0 h_one_sub
    have h1_scaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤ t * (S.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left h1 ht0
    calc
      S.sum ((1 - t) • x0 + t • x1) - (Finset.univ \ S).sum ((1 - t) • x0 + t • x1) =
          (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) +
            t * (S.sum x1 - (Finset.univ \ S).sum x1) := by
              simpa using odd_set_left_side_weighted_combination S x0 x1 t
      _ ≤ (1 - t) * ((S.card : ℝ) - 1) + t * (S.card : ℝ) := add_le_add h0_scaled h1_scaled
      _ = (S.card : ℝ) - 1 + t := by ring
  · intro S hSeven
    -- On even subsets, the roles of the sharp and weak bounds are swapped.
    have h0 :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx0_box S
    have h1 :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx1_ineq) ⟨S, hSeven⟩
    have h0_scaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤ (1 - t) * (S.card : ℝ) := by
      have h_one_sub : 0 ≤ 1 - t := by linarith
      exact mul_le_mul_of_nonneg_left h0 h_one_sub
    have h1_scaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤ t * ((S.card : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left h1 ht0
    calc
      S.sum ((1 - t) • x0 + t • x1) - (Finset.univ \ S).sum ((1 - t) • x0 + t • x1) =
          (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) +
            t * (S.sum x1 - (Finset.univ \ S).sum x1) := by
              simpa using odd_set_left_side_weighted_combination S x0 x1 t
      _ ≤ (1 - t) * (S.card : ℝ) + t * ((S.card : ℝ) - 1) := add_le_add h0_scaled h1_scaled
      _ = (S.card : ℝ) - t := by ring

/-- Helper for Theorem 4.46: every weighted combination of an even-polyhedron point and an
odd-polyhedron point satisfies the normalized even fixed-slice system. -/
lemma weighted_combination_subset_even_prefix_slice (n : ℕ) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    {x | ∃ x0 ∈ even_set_polyhedron n, ∃ x1 ∈ odd_set_polyhedron n,
      x = (1 - t) • x0 + t • x1} ⊆ even_prefix_slice n t := by
  intro x hx
  rcases hx with ⟨x0, hx0, x1, hx1, rfl⟩
  rcases hx0 with ⟨hx0_box, hx0_ineq⟩
  rcases hx1 with ⟨hx1_box, hx1_ineq⟩
  refine ⟨?_, ?_, ?_⟩
  · -- The same convex-box argument works for the parity-swapped slice.
    constructor
    · intro i
      have hx0i : 0 ≤ x0 i := hx0_box.1 i
      have hx1i : 0 ≤ x1 i := hx1_box.1 i
      have h_one_sub : 0 ≤ 1 - t := by linarith
      have h0 : 0 ≤ (1 - t) * x0 i := mul_nonneg h_one_sub hx0i
      have h1 : 0 ≤ t * x1 i := mul_nonneg ht0 hx1i
      simpa [Pi.smul_apply] using add_nonneg h0 h1
    · intro i
      have hx0i : x0 i ≤ 1 := hx0_box.2 i
      have hx1i : x1 i ≤ 1 := hx1_box.2 i
      have h_one_sub : 0 ≤ 1 - t := by linarith
      have h0 : (1 - t) * x0 i ≤ 1 - t := by
        simpa using mul_le_mul_of_nonneg_left hx0i h_one_sub
      have h1 : t * x1 i ≤ t := by
        simpa using mul_le_mul_of_nonneg_left hx1i ht0
      have hsum : (1 - t) * x0 i + t * x1 i ≤ (1 - t) + t := add_le_add h0 h1
      simpa [Pi.smul_apply] using hsum.trans_eq (by ring)
  · intro S hSodd
    -- For the even slice, odd subsets use the weak bound on the even endpoint and the sharp bound
    -- on the odd endpoint.
    have h0 :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx0_box S
    have h1 :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx1_ineq) ⟨S, hSodd⟩
    have h0_scaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤ (1 - t) * (S.card : ℝ) := by
      have h_one_sub : 0 ≤ 1 - t := by linarith
      exact mul_le_mul_of_nonneg_left h0 h_one_sub
    have h1_scaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤ t * ((S.card : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left h1 ht0
    calc
      S.sum ((1 - t) • x0 + t • x1) - (Finset.univ \ S).sum ((1 - t) • x0 + t • x1) =
          (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) +
            t * (S.sum x1 - (Finset.univ \ S).sum x1) := by
              simpa using odd_set_left_side_weighted_combination S x0 x1 t
      _ ≤ (1 - t) * (S.card : ℝ) + t * ((S.card : ℝ) - 1) := add_le_add h0_scaled h1_scaled
      _ = (S.card : ℝ) - t := by ring
  · intro S hSeven
    -- On even subsets, the even endpoint contributes the sharp bound and the odd endpoint only
    -- the weak box bound.
    have h0 :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx0_ineq) ⟨S, hSeven⟩
    have h1 :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx1_box S
    have h0_scaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤ (1 - t) * ((S.card : ℝ) - 1) := by
      have h_one_sub : 0 ≤ 1 - t := by linarith
      exact mul_le_mul_of_nonneg_left h0 h_one_sub
    have h1_scaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤ t * (S.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left h1 ht0
    calc
      S.sum ((1 - t) • x0 + t • x1) - (Finset.univ \ S).sum ((1 - t) • x0 + t • x1) =
          (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) +
            t * (S.sum x1 - (Finset.univ \ S).sum x1) := by
              simpa using odd_set_left_side_weighted_combination S x0 x1 t
      _ ≤ (1 - t) * ((S.card : ℝ) - 1) + t * (S.card : ℝ) := add_le_add h0_scaled h1_scaled
      _ = (S.card : ℝ) - 1 + t := by ring

/-- Helper for Theorem 4.46: the boundary slices `t = 0, 1` are exactly the prefix odd/even
polyhedra obtained from the corresponding `Fin.snoc` boundary points. -/
lemma prefix_slice_endpoint_eq_parity_polyhedron (n : ℕ) :
    (odd_prefix_slice n 0 = odd_set_polyhedron n) ∧
      (odd_prefix_slice n 1 = even_set_polyhedron n) ∧
      (even_prefix_slice n 0 = even_set_polyhedron n) ∧
      (even_prefix_slice n 1 = odd_set_polyhedron n) := by
  constructor
  · ext x
    -- Route correction: the degenerate parameters are handled by the exact `Fin.snoc` boundary
    -- slice equivalences, so the later weighted-combination lemmas only need the interior case.
    have hslice :
        Fin.snoc x 0 ∈ odd_set_polyhedron (n + 1) ↔ x ∈ odd_prefix_slice n 0 := by
      simpa using (snoc_mem_parity_polyhedron_iff_prefix_slice x 0).1
    exact hslice.symm.trans (odd_set_polyhedron_snoc_slices (x := x)).1
  constructor
  · ext x
    -- The `t = 1` odd slice is the `snoc 1` branch of the odd ambient polyhedron.
    have hslice :
        Fin.snoc x 1 ∈ odd_set_polyhedron (n + 1) ↔ x ∈ odd_prefix_slice n 1 := by
      simpa using (snoc_mem_parity_polyhedron_iff_prefix_slice x 1).1
    exact hslice.symm.trans (odd_set_polyhedron_snoc_slices (x := x)).2
  constructor
  · ext x
    -- The `t = 0` even slice is the `snoc 0` branch of the even ambient polyhedron.
    have hslice :
        Fin.snoc x 0 ∈ even_set_polyhedron (n + 1) ↔ x ∈ even_prefix_slice n 0 := by
      simpa using (snoc_mem_parity_polyhedron_iff_prefix_slice x 0).2
    exact hslice.symm.trans (even_set_polyhedron_snoc_slices (x := x)).1
  · ext x
    -- The `t = 1` even slice is the `snoc 1` branch of the even ambient polyhedron.
    have hslice :
        Fin.snoc x 1 ∈ even_set_polyhedron (n + 1) ↔ x ∈ even_prefix_slice n 1 := by
      simpa using (snoc_mem_parity_polyhedron_iff_prefix_slice x 1).2
    exact hslice.symm.trans (even_set_polyhedron_snoc_slices (x := x)).2

/-- Helper for Theorem 4.46: scaling a prefix vector scales the odd-set left-hand side by the
same scalar. -/
lemma odd_set_left_side_smul {n : ℕ} (S : Finset (Fin n)) (a : ℝ) (x : Fin n → ℝ) :
    S.sum (a • x) - (Finset.univ \ S).sum (a • x) =
      a * (S.sum x - (Finset.univ \ S).sum x) := by
  -- Expand the pointwise scalar multiplication inside each sum and factor out the common scalar.
  calc
    S.sum (a • x) - (Finset.univ \ S).sum (a • x) =
        (∑ i ∈ S, a * x i) - ∑ i ∈ (Finset.univ \ S), a * x i := by
          simp [Pi.smul_apply, smul_eq_mul]
    _ = a * S.sum x - a * (Finset.univ \ S).sum x := by
          rw [← Finset.mul_sum, ← Finset.mul_sum]
    _ = a * (S.sum x - (Finset.univ \ S).sum x) := by
          ring

/-- Helper for Theorem 4.46: the odd-set left-hand side is additive in the underlying vector. -/
lemma odd_set_left_side_add {n : ℕ} (S : Finset (Fin n)) (x0 x1 : Fin n → ℝ) :
    S.sum (x0 + x1) - (Finset.univ \ S).sum (x0 + x1) =
      (S.sum x0 - (Finset.univ \ S).sum x0) +
        (S.sum x1 - (Finset.univ \ S).sum x1) := by
  -- Expand both finite sums through pointwise addition and then regroup the four terms.
  simp [Pi.add_apply, Finset.sum_add_distrib]
  ring

/-- Helper for Theorem 4.46: dividing a positively scaled odd endpoint witness by its weight
recovers a point of the odd endpoint polyhedron. -/
lemma scaled_mem_odd_set_polyhedron_of_positive_weight {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {y : Fin n → ℝ}
    (hy_lower : ∀ i, 0 ≤ y i)
    (hy_upper : ∀ i, y i ≤ δ)
    (hy_odd :
      ∀ S : Finset (Fin n), Odd S.card →
        S.sum y - (Finset.univ \ S).sum y ≤ δ * ((S.card : ℝ) - 1)) :
    δ⁻¹ • y ∈ odd_set_polyhedron n := by
  refine ⟨?_, ?_⟩
  · -- Divide the scaled box constraints by the positive weight `δ`.
    constructor
    · intro i
      have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hδinv_nonneg (hy_lower i)
    · intro i
      have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      have hmul : δ⁻¹ * y i ≤ δ⁻¹ * δ := by
        exact mul_le_mul_of_nonneg_left (hy_upper i) hδinv_nonneg
      simpa [Pi.smul_apply, smul_eq_mul, hδ.ne', inv_mul_cancel₀] using hmul
  · -- Route correction: once the source slice is split into scaled endpoint systems, each odd-set
    -- row is rescaled separately instead of trying to normalize the full interpolated system at
    -- once.
    rw [Set.mem_iInter]
    intro S
    have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hscaled :
        δ⁻¹ * (S.1.sum y - (Finset.univ \ S.1).sum y) ≤
          δ⁻¹ * (δ * ((S.1.card : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (hy_odd S.1 S.2) hδinv_nonneg
    calc
      S.1.sum (δ⁻¹ • y) - (Finset.univ \ S.1).sum (δ⁻¹ • y) =
          δ⁻¹ * (S.1.sum y - (Finset.univ \ S.1).sum y) := by
            simpa using odd_set_left_side_smul S.1 δ⁻¹ y
      _ ≤ δ⁻¹ * (δ * ((S.1.card : ℝ) - 1)) := hscaled
      _ = (S.1.card : ℝ) - 1 := by
            rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]

/-- Helper for Theorem 4.46: dividing a positively scaled even endpoint witness by its weight
recovers a point of the even endpoint polyhedron. -/
lemma scaled_mem_even_set_polyhedron_of_positive_weight {n : ℕ} {δ : ℝ}
    (hδ : 0 < δ) {y : Fin n → ℝ}
    (hy_lower : ∀ i, 0 ≤ y i)
    (hy_upper : ∀ i, y i ≤ δ)
    (hy_even :
      ∀ S : Finset (Fin n), Even S.card →
        S.sum y - (Finset.univ \ S).sum y ≤ δ * ((S.card : ℝ) - 1)) :
    δ⁻¹ • y ∈ even_set_polyhedron n := by
  refine ⟨?_, ?_⟩
  · -- The scaled even endpoint system has the same box normalization as the odd one.
    constructor
    · intro i
      have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg hδinv_nonneg (hy_lower i)
    · intro i
      have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
      have hmul : δ⁻¹ * y i ≤ δ⁻¹ * δ := by
        exact mul_le_mul_of_nonneg_left (hy_upper i) hδinv_nonneg
      simpa [Pi.smul_apply, smul_eq_mul, hδ.ne', inv_mul_cancel₀] using hmul
  · -- The parity-swapped endpoint system rescales in the same one-row-at-a-time way.
    rw [Set.mem_iInter]
    intro S
    have hδinv_nonneg : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
    have hscaled :
        δ⁻¹ * (S.1.sum y - (Finset.univ \ S.1).sum y) ≤
          δ⁻¹ * (δ * ((S.1.card : ℝ) - 1)) := by
      exact mul_le_mul_of_nonneg_left (hy_even S.1 S.2) hδinv_nonneg
    calc
      S.1.sum (δ⁻¹ • y) - (Finset.univ \ S.1).sum (δ⁻¹ • y) =
          δ⁻¹ * (S.1.sum y - (Finset.univ \ S.1).sum y) := by
            simpa using odd_set_left_side_smul S.1 δ⁻¹ y
      _ ≤ δ⁻¹ * (δ * ((S.1.card : ℝ) - 1)) := hscaled
      _ = (S.1.card : ℝ) - 1 := by
            rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]

/-- Helper for Theorem 4.46: endpoint witnesses can be repackaged into the older scaled split
normal form by taking the two weighted parts separately. -/
lemma weightedParityEndpointsToScaledOddEvenSplit {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x x0 x1 : Fin n → ℝ}
    (hx0 : x0 ∈ odd_set_polyhedron n) (hx1 : x1 ∈ even_set_polyhedron n)
    (hx : x = (1 - t) • x0 + t • x1) :
    ∃ y0 y1,
      x = y0 + y1 ∧
      (∀ i, 0 ≤ y0 i) ∧
      (∀ i, y0 i ≤ 1 - t) ∧
      (∀ i, 0 ≤ y1 i) ∧
      (∀ i, y1 i ≤ t) ∧
      (∀ S : Finset (Fin n), Odd S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * ((S.card : ℝ) - 1)) ∧
      (∀ S : Finset (Fin n), Even S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * (S.card : ℝ)) ∧
      (∀ S : Finset (Fin n), Odd S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * (S.card : ℝ)) ∧
      (∀ S : Finset (Fin n), Even S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * ((S.card : ℝ) - 1)) := by
  rcases hx0 with ⟨hx0_box, hx0_ineq⟩
  rcases hx1 with ⟨hx1_box, hx1_ineq⟩
  refine ⟨(1 - t) • x0, t • x1, ?_⟩
  have h_one_sub : 0 ≤ 1 - t := by
    linarith
  refine ⟨by simp [hx], ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    -- The odd endpoint box rescales coordinatewise by the nonnegative factor `1 - t`.
    have hx0i : 0 ≤ x0 i := hx0_box.1 i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg h_one_sub hx0i
  · intro i
    -- The upper odd endpoint box bound rescales to the target upper bound `1 - t`.
    have hx0i : x0 i ≤ 1 := hx0_box.2 i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hx0i h_one_sub
  · intro i
    -- The even endpoint box rescales coordinatewise by the nonnegative factor `t`.
    have hx1i : 0 ≤ x1 i := hx1_box.1 i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_nonneg ht0 hx1i
  · intro i
    -- The upper even endpoint box bound rescales to the target upper bound `t`.
    have hx1i : x1 i ≤ 1 := hx1_box.2 i
    simpa [Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left hx1i ht0
  · intro S hSodd
    -- On odd rows, the odd endpoint contributes its sharp bound after scaling by `1 - t`.
    have hrow :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx0_ineq) ⟨S, hSodd⟩
    have hscaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤
          (1 - t) * ((S.card : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left hrow h_one_sub
    simpa using (odd_set_left_side_smul S (1 - t) x0).trans_le hscaled
  · intro S hSeven
    -- On even rows, the odd endpoint only needs the weak box bound before scaling.
    have hrow :
        S.sum x0 - (Finset.univ \ S).sum x0 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx0_box S
    have hscaled :
        (1 - t) * (S.sum x0 - (Finset.univ \ S).sum x0) ≤
          (1 - t) * (S.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hrow h_one_sub
    simpa using (odd_set_left_side_smul S (1 - t) x0).trans_le hscaled
  · intro S hSodd
    -- On odd rows, the even endpoint again only needs the weak box bound before scaling.
    have hrow :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ S.card := by
      exact odd_set_inequality_upper_bound_of_mem_box hx1_box S
    have hscaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤ t * (S.card : ℝ) := by
      exact mul_le_mul_of_nonneg_left hrow ht0
    simpa using (odd_set_left_side_smul S t x1).trans_le hscaled
  · intro S hSeven
    -- On even rows, the even endpoint contributes its sharp bound after scaling by `t`.
    have hrow :
        S.sum x1 - (Finset.univ \ S).sum x1 ≤ (S.card : ℝ) - 1 := by
      exact (Set.mem_iInter.mp hx1_ineq) ⟨S, hSeven⟩
    have hscaled :
        t * (S.sum x1 - (Finset.univ \ S).sum x1) ≤
          t * ((S.card : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left hrow ht0
    simpa using (odd_set_left_side_smul S t x1).trans_le hscaled

/-- Helper for Theorem 4.46: once the odd interior slice is decomposed into scaled odd/even
endpoint systems, rescaling the two parts gives the weighted endpoint witnesses. -/
lemma scaled_odd_even_split_to_weighted_combination {n : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {x y0 y1 : Fin n → ℝ}
    (hsum : x = y0 + y1)
    (hy0_lower : ∀ i, 0 ≤ y0 i)
    (hy0_upper : ∀ i, y0 i ≤ 1 - t)
    (hy1_lower : ∀ i, 0 ≤ y1 i)
    (hy1_upper : ∀ i, y1 i ≤ t)
    (hy0_odd :
      ∀ S : Finset (Fin n), Odd S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * ((S.card : ℝ) - 1))
    (_hy0_even :
      ∀ S : Finset (Fin n), Even S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * (S.card : ℝ))
    (_hy1_odd :
      ∀ S : Finset (Fin n), Odd S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * (S.card : ℝ))
    (hy1_even :
      ∀ S : Finset (Fin n), Even S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * ((S.card : ℝ) - 1)) :
    ∃ x0 ∈ odd_set_polyhedron n, ∃ x1 ∈ even_set_polyhedron n,
      x = (1 - t) • x0 + t • x1 := by
  let x0 : Fin n → ℝ := (1 - t)⁻¹ • y0
  let x1 : Fin n → ℝ := t⁻¹ • y1
  have h_one_sub : 0 < 1 - t := by
    linarith
  have hx0 : x0 ∈ odd_set_polyhedron n := by
    -- Normalize the scaled odd endpoint constraints by dividing through by `1 - t`.
    exact
      scaled_mem_odd_set_polyhedron_of_positive_weight h_one_sub hy0_lower hy0_upper hy0_odd
  have hx1 : x1 ∈ even_set_polyhedron n := by
    -- Normalize the scaled even endpoint constraints by dividing through by `t`.
    exact scaled_mem_even_set_polyhedron_of_positive_weight ht0 hy1_lower hy1_upper hy1_even
  refine ⟨x0, hx0, x1, hx1, ?_⟩
  -- Reassemble the two normalized endpoint witnesses into the original weighted combination.
  calc
    x = y0 + y1 := hsum
    _ = (1 - t) • x0 + t • x1 := by
          ext i
          -- Cancel each positive scaling factor against its inverse one coordinate at a time.
          have hy0' : y0 i = (1 - t) * x0 i := by
            calc
              y0 i = 1 * y0 i := by ring
              _ = ((1 - t) * (1 - t)⁻¹) * y0 i := by
                    rw [mul_inv_cancel₀ h_one_sub.ne']
              _ = (1 - t) * x0 i := by
                    simp [x0, Pi.smul_apply, smul_eq_mul, mul_assoc]
          have hy1' : y1 i = t * x1 i := by
            calc
              y1 i = 1 * y1 i := by ring
              _ = (t * t⁻¹) * y1 i := by
                    rw [mul_inv_cancel₀ ht0.ne']
              _ = t * x1 i := by
                    simp [x1, Pi.smul_apply, smul_eq_mul, mul_assoc]
          calc
            y0 i + y1 i = (1 - t) * x0 i + t * x1 i := by rw [hy0', hy1']
            _ = ((1 - t) • x0 + t • x1) i := by
                  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Helper for Theorem 4.46: the parity-swapped scaled split for the even interior slice also
rescales to weighted endpoint witnesses. -/
lemma scaled_even_odd_split_to_weighted_combination {n : ℕ} {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) {x y0 y1 : Fin n → ℝ}
    (hsum : x = y0 + y1)
    (hy0_lower : ∀ i, 0 ≤ y0 i)
    (hy0_upper : ∀ i, y0 i ≤ 1 - t)
    (hy1_lower : ∀ i, 0 ≤ y1 i)
    (hy1_upper : ∀ i, y1 i ≤ t)
    (_hy0_odd :
      ∀ S : Finset (Fin n), Odd S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * (S.card : ℝ))
    (hy0_even :
      ∀ S : Finset (Fin n), Even S.card →
        S.sum y0 - (Finset.univ \ S).sum y0 ≤ (1 - t) * ((S.card : ℝ) - 1))
    (hy1_odd :
      ∀ S : Finset (Fin n), Odd S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * ((S.card : ℝ) - 1))
    (_hy1_even :
      ∀ S : Finset (Fin n), Even S.card →
        S.sum y1 - (Finset.univ \ S).sum y1 ≤ t * (S.card : ℝ)) :
    ∃ x0 ∈ even_set_polyhedron n, ∃ x1 ∈ odd_set_polyhedron n,
    x = (1 - t) • x0 + t • x1 := by
  let x0 : Fin n → ℝ := (1 - t)⁻¹ • y0
  let x1 : Fin n → ℝ := t⁻¹ • y1
  have h_one_sub : 0 < 1 - t := by
    linarith
  have hx0 : x0 ∈ even_set_polyhedron n := by
    -- The even endpoint witness uses the parity-swapped scaled system for the `1 - t` block.
    exact
      scaled_mem_even_set_polyhedron_of_positive_weight h_one_sub hy0_lower hy0_upper hy0_even
  have hx1 : x1 ∈ odd_set_polyhedron n := by
    -- The odd endpoint witness uses the parity-swapped scaled system for the `t` block.
    exact scaled_mem_odd_set_polyhedron_of_positive_weight ht0 hy1_lower hy1_upper hy1_odd
  refine ⟨x0, hx0, x1, hx1, ?_⟩
  -- The reconstruction algebra is identical to the odd/even case above.
  calc
    x = y0 + y1 := hsum
    _ = (1 - t) • x0 + t • x1 := by
          ext i
          -- Cancel each positive scaling factor against its inverse one coordinate at a time.
          have hy0' : y0 i = (1 - t) * x0 i := by
            calc
              y0 i = 1 * y0 i := by ring
              _ = ((1 - t) * (1 - t)⁻¹) * y0 i := by
                    rw [mul_inv_cancel₀ h_one_sub.ne']
              _ = (1 - t) * x0 i := by
                    simp [x0, Pi.smul_apply, smul_eq_mul, mul_assoc]
          have hy1' : y1 i = t * x1 i := by
            calc
              y1 i = 1 * y1 i := by ring
              _ = (t * t⁻¹) * y1 i := by
                    rw [mul_inv_cancel₀ ht0.ne']
              _ = t * x1 i := by
                    simp [x1, Pi.smul_apply, smul_eq_mul, mul_assoc]
          calc
            y0 i + y1 i = (1 - t) * x0 i + t * x1 i := by rw [hy0', hy1']
            _ = ((1 - t) • x0 + t • x1) i := by
                  simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul]

/-- Helper for Theorem 4.46: replacing `t` by `1 - t` swaps the odd and even fixed-slice
systems. -/
lemma even_prefix_slice_eq_odd_prefix_slice_one_sub (n : ℕ) (t : ℝ) :
    even_prefix_slice n t = odd_prefix_slice n (1 - t) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hx_box, hx_odd, hx_even⟩
    refine ⟨hx_box, ?_, ?_⟩
    · intro S hSodd
      -- The odd-row bound in the even slice is exactly the odd-row bound in the odd slice at
      -- parameter `1 - t`.
      have hrow := hx_odd S hSodd
      linarith
    · intro S hSeven
      -- The even-row bound rewrites in the same way after substituting `1 - t`.
      have hrow := hx_even S hSeven
      linarith
  · intro hx
    rcases hx with ⟨hx_box, hx_odd, hx_even⟩
    refine ⟨hx_box, ?_, ?_⟩
    · intro S hSodd
      -- Reversing the substitution recovers the odd-row system of the even slice.
      have hrow := hx_odd S hSodd
      linarith
    · intro S hSeven
      -- Reversing the substitution also recovers the even-row system.
      have hrow := hx_even S hSeven
      linarith

/-- Helper for Theorem 4.46: every point of the unit box splits into a `(1 - t)`-capped part and
a `t`-capped part. -/
lemma existsCappedSplitOfMemBox {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : Fin n → ℝ}
    (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    ∃ y0 y1,
      x = y0 + y1 ∧
      (∀ i, 0 ≤ y0 i) ∧
      (∀ i, y0 i ≤ 1 - t) ∧
      (∀ i, 0 ≤ y1 i) ∧
      (∀ i, y1 i ≤ t) := by
  let y0 : Fin n → ℝ := fun i ↦ max (x i - t) 0
  let y1 : Fin n → ℝ := fun i ↦ x i - y0 i
  rcases hx with ⟨hx_lower, hx_upper⟩
  refine ⟨y0, y1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- The two capped coordinatewise pieces reassemble to the original box point.
    ext i
    by_cases hxt : x i ≤ t
    · have hy0_eq : y0 i = 0 := by
        simp [y0, sub_nonpos.mpr hxt]
      simp [y1, hy0_eq]
    · have hxt' : t < x i := lt_of_not_ge hxt
      have hy0_eq : y0 i = x i - t := by
        simpa [y0] using max_eq_left (sub_nonneg.mpr hxt'.le)
      simp [y1, hy0_eq]
  · intro i
    -- The capped `(1 - t)` block is nonnegative by construction.
    simp [y0]
  · intro i
    -- The upper bound comes from `x i ≤ 1` together with `0 ≤ 1 - t`.
    have h_one_sub : 0 ≤ 1 - t := by
      linarith
    have hsub : x i - t ≤ 1 - t := by
      have hx_upper_i : x i ≤ 1 := hx_upper i
      linarith
    exact max_le_iff.mpr ⟨hsub, h_one_sub⟩
  · intro i
    -- The residual `t`-block is nonnegative in both threshold cases.
    by_cases hxt : x i ≤ t
    · have hy0_eq : y0 i = 0 := by
        simp [y0, sub_nonpos.mpr hxt]
      simpa [y1, hy0_eq] using hx_lower i
    · have hxt' : t < x i := lt_of_not_ge hxt
      have hy0_eq : y0 i = x i - t := by
        simpa [y0] using max_eq_left (sub_nonneg.mpr hxt'.le)
      simpa [y1, hy0_eq] using ht0
  · intro i
    -- The residual piece is either `x i` itself or exactly the threshold value `t`.
    by_cases hxt : x i ≤ t
    · have hy0_eq : y0 i = 0 := by
        simp [y0, sub_nonpos.mpr hxt]
      simpa [y1, hy0_eq] using hxt
    · have hxt' : t < x i := lt_of_not_ge hxt
      have hy0_eq : y0 i = x i - t := by
        simpa [y0] using max_eq_left (sub_nonneg.mpr hxt'.le)
      simp [y1, hy0_eq]

/-- Helper for Theorem 4.46: the box part of an odd fixed-slice point already admits the scaled
two-block decomposition. -/
lemma existsScaledBoxSplitOfMemOddPrefixSlice {n : ℕ} {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {x : Fin n → ℝ}
    (hx : x ∈ odd_prefix_slice n t) :
    ∃ y0 y1,
      x = y0 + y1 ∧
      (∀ i, 0 ≤ y0 i) ∧
      (∀ i, y0 i ≤ 1 - t) ∧
      (∀ i, 0 ≤ y1 i) ∧
      (∀ i, y1 i ≤ t) := by
  -- Only the box component of the odd slice is needed for this setup lemma.
  exact existsCappedSplitOfMemBox ht0 ht1 hx.1

/-- Helper for Theorem 4.46: the explicit threshold-capped split already supplies the box part of
the later odd/even decomposition. -/
lemma oddPrefixCappedSplitSpec {n : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {x : Fin n → ℝ} (hx : x ∈ Set.Icc (0 : Fin n → ℝ) 1) :
    let y0 : Fin n → ℝ := fun i ↦ max (x i - t) 0
    let y1 : Fin n → ℝ := fun i ↦ min (x i) t
    x = y0 + y1 ∧
      (∀ i, 0 ≤ y0 i) ∧
      (∀ i, y0 i ≤ 1 - t) ∧
      (∀ i, 0 ≤ y1 i) ∧
      (∀ i, y1 i ≤ t) := by
  let y0 : Fin n → ℝ := fun i ↦ max (x i - t) 0
  let y1 : Fin n → ℝ := fun i ↦ min (x i) t
  rcases hx with ⟨hx_lower, hx_upper⟩
  have hsum : x = y0 + y1 := by
    -- Split each coordinate at the threshold `t`; above it the `y0` branch carries the excess and
    -- below it the `y1` branch carries the whole coordinate.
    ext i
    by_cases hxt : x i ≤ t
    · have hy0_eq : y0 i = 0 := by
        simp [y0, sub_nonpos.mpr hxt]
      have hy1_eq : y1 i = x i := by
        simp [y1, hxt]
      simp [Pi.add_apply, hy0_eq, hy1_eq]
    · have hxt' : t < x i := lt_of_not_ge hxt
      have hy0_eq : y0 i = x i - t := by
        simpa [y0] using max_eq_left (sub_nonneg.mpr hxt'.le)
      have hy1_eq : y1 i = t := by
        simp [y1, hxt'.le]
      have hx_split : x i = (x i - t) + t := by ring
      rw [Pi.add_apply, hy0_eq, hy1_eq]
      exact hx_split
  have hy0_lower : ∀ i, 0 ≤ y0 i := by
    -- The positive branch is a maximum with `0`, so it is nonnegative coordinatewise.
    intro i
    simp [y0]
  have hy0_upper : ∀ i, y0 i ≤ 1 - t := by
    -- The box bound `x i ≤ 1` forces the threshold excess to stay below `1 - t`.
    intro i
    have hsub : x i - t ≤ 1 - t := by
      have hx_upper_i : x i ≤ 1 := hx_upper i
      linarith
    have h_one_sub : 0 ≤ 1 - t := by
      linarith
    exact max_le_iff.mpr ⟨hsub, h_one_sub⟩
  have hy1_lower : ∀ i, 0 ≤ y1 i := by
    -- The lower box bound and `t ≥ 0` imply the minimum branch is still nonnegative.
    intro i
    simpa [y1] using (le_min (hx_lower i) ht0 : 0 ≤ min (x i) t)
  have hy1_upper : ∀ i, y1 i ≤ t := by
    -- The minimum branch is bounded above by the threshold by definition.
    intro i
    change min (x i) t ≤ t
    exact min_le_right (x i) t
  simpa [y0, y1] using
    (show x = y0 + y1 ∧
        (∀ i, 0 ≤ y0 i) ∧
        (∀ i, y0 i ≤ 1 - t) ∧
        (∀ i, 0 ≤ y1 i) ∧
        (∀ i, y1 i ≤ t) from
      ⟨hsum, hy0_lower, hy0_upper, hy1_lower, hy1_upper⟩)

/-- Helper for Theorem 4.46: a box with upper bound `δ` gives the weak odd-set row bound
`δ * |S|`. -/
lemma odd_set_inequality_upper_bound_of_mem_scaled_box {n : ℕ} {δ : ℝ}
    {x : Fin n → ℝ} (hx_lower : ∀ i, 0 ≤ x i) (hx_upper : ∀ i, x i ≤ δ)
    (S : Finset (Fin n)) :
    S.sum x - (Finset.univ \ S).sum x ≤ δ * S.card := by
  have hsum_le : S.sum x ≤ δ * S.card := by
    calc
      S.sum x ≤ S.sum (fun _ : Fin n ↦ δ) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact hx_upper i
      _ = δ * S.card := by
        simp [mul_comm]
  have hcomp_nonneg : (0 : ℝ) ≤ (Finset.univ \ S).sum x := by
    exact Finset.sum_nonneg fun i hi ↦ hx_lower i
  linarith

/-- Helper for Theorem 4.46: the rational row type collecting the lower-box, upper-box, and
odd-set inequalities. -/
private abbrev oddSetRow (n : ℕ) :=
  (Fin n ⊕ Fin n) ⊕ odd_subset n

/-- Helper for Theorem 4.46: the rational matrix encoding the odd-set system together with the
box constraints. -/
private def oddSetPresentationMatrix (n : ℕ) : Matrix (oddSetRow n) (Fin n) ℚ
  | Sum.inl (Sum.inl i), j => if j = i then -1 else 0
  | Sum.inl (Sum.inr i), j => if j = i then 1 else 0
  | Sum.inr S, j => if j ∈ S.1 then 1 else -1

/-- Helper for Theorem 4.46: the rational right-hand side of the finite odd-set presentation. -/
private def oddSetPresentationRhs (n : ℕ) : oddSetRow n → ℚ
  | Sum.inl (Sum.inl _) => 0
  | Sum.inl (Sum.inr _) => 1
  | Sum.inr S => (S.1.card : ℚ) - 1

/-- Helper for Theorem 4.46: the odd-set polyhedron is a rational polyhedron. -/
private lemma odd_set_polyhedron_is_rational_polyhedron (n : ℕ) :
    is_rational_polyhedron (odd_set_polyhedron n) := by
  classical
  let ρ := oddSetRow n
  let A : Matrix (Fin (Fintype.card ρ)) (Fin n) ℚ :=
    Matrix.reindex (Fintype.equivFin ρ) (Equiv.refl _) (oddSetPresentationMatrix n)
  let b : Fin (Fintype.card ρ) → ℚ :=
    oddSetPresentationRhs n ∘ (Fintype.equivFin ρ).symm
  rw [is_rational_polyhedron_iff]
  refine ⟨Fintype.card ρ, A, b, ?_⟩
  ext x
  constructor
  · intro hx
    rcases hx with ⟨hbox, hineq⟩
    intro i
    rcases hrowEq : (Fintype.equivFin ρ).symm i with (r | r) | S
    · have hEval :
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) = -x r := by
        calc
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) =
              ∑ j, (((if j = r then (-1 : ℚ) else 0 : ℚ) : ℝ) * x j) := by
                simp [hrowEq, A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec,
                  dotProduct]
          _ = ∑ j, if j = r then -x j else 0 := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases h : j = r <;> simp [h]
          _ = -x r := by
                simp
      have hrow : -x r ≤ 0 := by
        exact neg_nonpos.mpr (hbox.1 r)
      have hRhs : (fun i ↦ (b i : ℝ)) i = 0 := by
        dsimp [b]
        rw [hrowEq]
        simp [oddSetPresentationRhs]
      rw [hEval, hRhs]
      exact hrow
    · have hEval :
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) = x r := by
        calc
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) =
              ∑ j, (((if j = r then (1 : ℚ) else 0 : ℚ) : ℝ) * x j) := by
                simp [hrowEq, A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec,
                  dotProduct]
          _ = ∑ j, if j = r then x j else 0 := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases h : j = r <;> simp [h]
          _ = x r := by
                simp
      have hRhs : (fun i ↦ (b i : ℝ)) i = 1 := by
        dsimp [b]
        rw [hrowEq]
        simp [oddSetPresentationRhs]
      rw [hEval, hRhs]
      exact hbox.2 r
    · have hEval :
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) =
            ∑ j, if j ∈ S.1 then x j else -x j := by
        calc
          (((A.map (Rat.castHom ℝ)).mulVec x) i : ℝ) =
              ∑ j, (((if j ∈ S.1 then (1 : ℚ) else -1 : ℚ) : ℝ) * x j) := by
                simp [hrowEq, A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec,
                  dotProduct]
          _ = ∑ j, if j ∈ S.1 then x j else -x j := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases h : j ∈ S.1 <;> simp [h]
      have hsum :
          (∑ j, if j ∈ S.1 then x j else -x j) =
            S.1.sum x - (Finset.univ \ S.1).sum x := by
        simp [Finset.sum_ite, Finset.sdiff_eq_filter, sub_eq_add_neg]
      have htarget :
          (∑ j, if j ∈ S.1 then x j else -x j) ≤ (S.1.card : ℝ) - 1 := by
        rw [hsum]
        exact (Set.mem_iInter.mp hineq) S
      have hRhs : (fun i ↦ (b i : ℝ)) i = (S.1.card : ℝ) - 1 := by
        dsimp [b]
        rw [hrowEq]
        simp [oddSetPresentationRhs]
      rw [hEval, hRhs]
      exact htarget
  · intro hx
    refine ⟨?_, ?_⟩
    · constructor
      · intro r
        have hr := hx ((Fintype.equivFin ρ) (Sum.inl (Sum.inl r)))
        have hEval :
            (((A.map (Rat.castHom ℝ)).mulVec x)
              ((Fintype.equivFin ρ) (Sum.inl (Sum.inl r))) : ℝ) = -x r := by
          calc
            (((A.map (Rat.castHom ℝ)).mulVec x)
                ((Fintype.equivFin ρ) (Sum.inl (Sum.inl r))) : ℝ) =
                ∑ j, (((if j = r then (-1 : ℚ) else 0 : ℚ) : ℝ) * x j) := by
                  simp [A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec,
                    dotProduct]
            _ = ∑ j, if j = r then -x j else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  by_cases h : j = r <;> simp [h]
            _ = -x r := by
                  simp
        have hrow : -x r ≤ 0 := by
          have hRhs :
              (fun i ↦ (b i : ℝ)) ((Fintype.equivFin ρ) (Sum.inl (Sum.inl r))) = 0 := by
            simp [b, oddSetPresentationRhs]
          rw [hEval, hRhs] at hr
          exact hr
        exact neg_nonpos.mp hrow
      · intro r
        have hr := hx ((Fintype.equivFin ρ) (Sum.inl (Sum.inr r)))
        have hEval :
            (((A.map (Rat.castHom ℝ)).mulVec x)
              ((Fintype.equivFin ρ) (Sum.inl (Sum.inr r))) : ℝ) = x r := by
          calc
            (((A.map (Rat.castHom ℝ)).mulVec x)
                ((Fintype.equivFin ρ) (Sum.inl (Sum.inr r))) : ℝ) =
                ∑ j, (((if j = r then (1 : ℚ) else 0 : ℚ) : ℝ) * x j) := by
                  simp [A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec,
                    dotProduct]
            _ = ∑ j, if j = r then x j else 0 := by
                  refine Finset.sum_congr rfl ?_
                  intro j hj
                  by_cases h : j = r <;> simp [h]
            _ = x r := by
                  simp
        have hRhs :
            (fun i ↦ (b i : ℝ)) ((Fintype.equivFin ρ) (Sum.inl (Sum.inr r))) = 1 := by
          simp [b, oddSetPresentationRhs]
        rw [hEval, hRhs] at hr
        exact hr
    · rw [Set.mem_iInter]
      intro S
      have hS := hx ((Fintype.equivFin ρ) (Sum.inr S))
      have hEval :
          (((A.map (Rat.castHom ℝ)).mulVec x) ((Fintype.equivFin ρ) (Sum.inr S)) : ℝ) =
            ∑ j, if j ∈ S.1 then x j else -x j := by
        calc
          (((A.map (Rat.castHom ℝ)).mulVec x) ((Fintype.equivFin ρ) (Sum.inr S)) : ℝ) =
              ∑ j, (((if j ∈ S.1 then (1 : ℚ) else -1 : ℚ) : ℝ) * x j) := by
                simp [A, oddSetPresentationMatrix, Matrix.reindex_apply, Matrix.mulVec, dotProduct]
          _ = ∑ j, if j ∈ S.1 then x j else -x j := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                by_cases h : j ∈ S.1 <;> simp [h]
      have htarget :
          (∑ j, if j ∈ S.1 then x j else -x j) ≤ (S.1.card : ℝ) - 1 := by
        have hRhs :
            (fun i ↦ (b i : ℝ)) ((Fintype.equivFin ρ) (Sum.inr S)) = (S.1.card : ℝ) - 1 := by
          simp [b, oddSetPresentationRhs]
        rw [hEval, hRhs] at hS
        exact hS
      have hsum :
          (∑ j, if j ∈ S.1 then x j else -x j) =
            S.1.sum x - (Finset.univ \ S.1).sum x := by
        simp [Finset.sum_ite, Finset.sdiff_eq_filter, sub_eq_add_neg]
      change odd_set_inequality S.1 x
      unfold odd_set_inequality
      rw [← hsum]
      exact htarget

/-- Helper for Theorem 4.46: every even `0/1` vector is an integer vector. -/
private lemma mem_integerVectors_of_even_zero_one_vectors {n : ℕ} {x : Fin n → ℝ}
    (hx : x ∈ even_zero_one_vectors n) :
    x ∈ ℤ^n := by
  rw [mem_integerVectors_iff_forall]
  intro i
  rcases hx.1 i with h0 | h1
  · exact ⟨0, by norm_num [h0]⟩
  · exact ⟨1, by norm_num [h1]⟩

/-- Helper for Theorem 4.46: an integer point of the odd-set polyhedron is one of the even
`0,1` vertices. -/
private lemma mem_even_zero_one_vectors_of_mem_odd_set_polyhedron_of_integer {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ odd_set_polyhedron n) (hxZ : x ∈ ℤ^n) :
    x ∈ even_zero_one_vectors n := by
  rcases (mem_integerVectors_iff.mp hxZ) with ⟨z, rfl⟩
  have hz01 : is_zero_one_vector (Int.cast ∘ z) := by
    intro i
    have hz0real : (0 : ℝ) ≤ (z i : ℝ) := by
      simpa using hx.1.1 i
    have hz1real : (z i : ℝ) ≤ 1 := by
      simpa using hx.1.2 i
    have hz0 : 0 ≤ z i := by
      exact_mod_cast hz0real
    have hz1 : z i ≤ 1 := by
      exact_mod_cast hz1real
    interval_cases h : z i <;> simp [h]
  refine ⟨hz01, ?_⟩
  by_contra hOdd
  let S : Finset (Fin n) := Finset.univ.filter fun i ↦ (Int.cast (z i) : ℝ) = 1
  have hSodd : Odd S.card := by
    simpa [S, one_coordinate_count] using Nat.not_even_iff_odd.mp hOdd
  have hineq : odd_set_inequality S (Int.cast ∘ z) := by
    exact (Set.mem_iInter.mp hx.2) ⟨S, hSodd⟩
  have hsumS : S.sum (Int.cast ∘ z) = (S.card : ℝ) := by
    calc
      S.sum (Int.cast ∘ z) =
          (((S.filter fun i ↦ (Int.cast (z i) : ℝ) = 1).card : ℕ) : ℝ) := by
            simpa using sum_eq_card_filter_of_zero_one (Int.cast ∘ z) S hz01
      _ = (S.card : ℝ) := by
            have hSfilter : S.filter (fun i ↦ (Int.cast (z i) : ℝ) = 1) = S := by
              ext i
              simp [S]
            rw [hSfilter]
  have hsumSc : ((Finset.univ \ S).sum (Int.cast ∘ z) : ℝ) = 0 := by
    refine Finset.sum_eq_zero ?_
    intro i hi
    rcases hz01 i with h0 | h1
    · exact_mod_cast h0
    · exfalso
      exact (Finset.mem_sdiff.mp hi).2 (by simpa [S] using h1)
  unfold odd_set_inequality at hineq
  rw [hsumS, hsumSc] at hineq
  linarith

/-- Helper for Theorem 4.46: the Chapter 3 optimizer produces an even `0,1` vertex. -/
private lemma evenParityOptimizer_mem_even_zero_one_vectors (n : ℕ) (c : Fin n → ℝ) (j : Fin n) :
    exercise_3_4_even_parity_optimizer c j ∈ even_zero_one_vectors n := by
  have hCube : exercise_3_4_even_parity_optimizer c j ∈ zero_one_cube n :=
    exercise_3_4_even_parity_optimizer_mem_zero_one_cube c j
  have hSupport :
      Finset.univ.filter (fun i : Fin n ↦ exercise_3_4_even_parity_optimizer c j i = 1) =
        exercise_3_4_even_parity_indices c j :=
    exercise_3_4_even_parity_optimizer_one_coordinates c j
  refine ⟨?_, ?_⟩
  · intro i
    exact (mem_zero_one_cube_iff.mp hCube) i
  · have hEven : Even (exercise_3_4_even_parity_indices c j).card :=
      exercise_3_4_even_parity_indices_even_card c j
    simpa [one_coordinate_count, hSupport] using hEven

/-- Helper for Theorem 4.46: the Chapter 3 optimizer value for `-c` is the positive-part sum, with
the minimum-absolute-cost parity correction in the odd case. -/
private lemma evenParityOptimizer_neg_value {n : ℕ} (c : Fin n → ℝ) (j : Fin n) :
    let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
    c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j =
      if Even P.card then P.sum c else P.sum c - |c j| := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
  let xopt := exercise_3_4_even_parity_optimizer (-c) j
  have hDotNeg :
      (-c) ⬝ᵥ xopt = Finset.sum (exercise_3_4_even_parity_indices (-c) j) (-c) := by
    rw [dotProduct_eq_sum_one_coordinates_of_mem_zero_one_cube (-c)
        (exercise_3_4_even_parity_optimizer_mem_zero_one_cube (-c) j),
      exercise_3_4_even_parity_optimizer_one_coordinates (-c) j]
  have hIndexSum :
      Finset.sum (exercise_3_4_even_parity_indices (-c) j) (-c) =
        if Even P.card then -(P.sum c) else -(P.sum c) + |c j| := by
    simpa [P, Finset.sum_neg_distrib, abs_neg] using
      exercise_3_4_even_parity_indices_sum (-c) j
  have hNegDot : (-c) ⬝ᵥ xopt = -(c ⬝ᵥ xopt) := by
    unfold dotProduct
    simp [Pi.neg_apply, Finset.sum_neg_distrib]
  have hOptNeg :
      (-c) ⬝ᵥ xopt = if Even P.card then -(P.sum c) else -(P.sum c) + |c j| := by
    rw [hDotNeg]
    exact hIndexSum
  by_cases hEvenP : Even P.card
  · have hneg : (-c) ⬝ᵥ xopt = -(P.sum c) := by simpa [hEvenP] using hOptNeg
    have hneg' : -(c ⬝ᵥ xopt) = -(P.sum c) := by simpa [hNegDot] using hneg
    have hEq : c ⬝ᵥ xopt = P.sum c := by linarith
    simpa [P, xopt, hEvenP] using hEq
  · have hneg : (-c) ⬝ᵥ xopt = -(P.sum c) + |c j| := by simpa [hEvenP] using hOptNeg
    have hneg' : -(c ⬝ᵥ xopt) = -(P.sum c) + |c j| := by simpa [hNegDot] using hneg
    have hEq : c ⬝ᵥ xopt = P.sum c - |c j| := by linarith
    simpa [P, xopt, hEvenP] using hEq

/-- Helper for Theorem 4.46: one odd-set inequality together with the box constraints bounds every
linear objective by the Chapter 3 even-parity optimizer. -/
private lemma dotProduct_le_evenParityOptimizer_of_mem_odd_set_polyhedron {n : ℕ}
    {x : Fin n → ℝ} (hx : x ∈ odd_set_polyhedron n)
    (c : Fin n → ℝ) (j : Fin n) (hj : ∀ i, |c j| ≤ |c i|) :
    c ⬝ᵥ x ≤ c ⬝ᵥ exercise_3_4_even_parity_optimizer (-c) j := by
  classical
  let P : Finset (Fin n) := Finset.univ.filter fun i ↦ 0 < c i
  let xopt := exercise_3_4_even_parity_optimizer (-c) j
  have hOptValue :
      c ⬝ᵥ xopt = if Even P.card then P.sum c else P.sum c - |c j| := by
    simpa [P, xopt] using evenParityOptimizer_neg_value c j
  have hDecomp :
      c ⬝ᵥ x = P.sum (fun i ↦ c i * x i) + (Finset.univ \ P).sum (fun i ↦ c i * x i) := by
    unfold dotProduct
    rw [← Finset.sum_sdiff (Finset.subset_univ P)]
    ring
  by_cases hEvenP : Even P.card
  · have hPos :
        P.sum (fun i ↦ c i * x i) ≤ P.sum c := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hci : 0 < c i := (Finset.mem_filter.mp hi).2
      have hxi0 : 0 ≤ x i := hx.1.1 i
      have hxi1 : x i ≤ 1 := hx.1.2 i
      nlinarith
    have hNonpos :
        (Finset.univ \ P).sum (fun i ↦ c i * x i) ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      have hci : c i ≤ 0 := by
        exact not_lt.mp fun hlt ↦ (Finset.mem_sdiff.mp hi).2 (by simp [P, hlt])
      have hxi0 : 0 ≤ x i := hx.1.1 i
      nlinarith
    have hBound : c ⬝ᵥ x ≤ P.sum c := by
      linarith
    calc
      c ⬝ᵥ x ≤ P.sum c := hBound
      _ = c ⬝ᵥ xopt := by simpa [hEvenP] using hOptValue.symm
  · have hOddP : Odd P.card := Nat.not_even_iff_odd.mp hEvenP
    have hOddRow : odd_set_inequality P x := by
      exact (Set.mem_iInter.mp hx.2) ⟨P, hOddP⟩
    have hScaled :
        |c j| * (P.sum x - (Finset.univ \ P).sum x) ≤ |c j| * ((P.card : ℝ) - 1) := by
      exact mul_le_mul_of_nonneg_left hOddRow (abs_nonneg _)
    have hPosDecomp :
        P.sum (fun i ↦ c i * x i) =
          |c j| * P.sum x + P.sum (fun i ↦ (c i - |c j|) * x i) := by
      calc
        P.sum (fun i ↦ c i * x i) =
            P.sum (fun i ↦ |c j| * x i + (c i - |c j|) * x i) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              ring
        _ = P.sum (fun i ↦ |c j| * x i) + P.sum (fun i ↦ (c i - |c j|) * x i) := by
              rw [Finset.sum_add_distrib]
        _ = |c j| * P.sum x + P.sum (fun i ↦ (c i - |c j|) * x i) := by
              rw [Finset.mul_sum]
    have hNegDecomp :
        (Finset.univ \ P).sum (fun i ↦ c i * x i) =
          -|c j| * (Finset.univ \ P).sum x +
            (Finset.univ \ P).sum (fun i ↦ (c i + |c j|) * x i) := by
      calc
        (Finset.univ \ P).sum (fun i ↦ c i * x i) =
            (Finset.univ \ P).sum
              (fun i ↦ (-|c j|) * x i + (c i + |c j|) * x i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                ring
        _ = (Finset.univ \ P).sum (fun i ↦ (-|c j|) * x i) +
              (Finset.univ \ P).sum (fun i ↦ (c i + |c j|) * x i) := by
                rw [Finset.sum_add_distrib]
        _ = -|c j| * (Finset.univ \ P).sum x +
              (Finset.univ \ P).sum (fun i ↦ (c i + |c j|) * x i) := by
                rw [Finset.mul_sum]
    have hPosResid :
        P.sum (fun i ↦ (c i - |c j|) * x i) ≤ P.sum (fun i ↦ c i - |c j|) := by
      refine Finset.sum_le_sum ?_
      intro i hi
      have hci : 0 < c i := (Finset.mem_filter.mp hi).2
      have hcoef : 0 ≤ c i - |c j| := by
        have hji : |c j| ≤ c i := by
          simpa [abs_of_pos hci] using hj i
        linarith
      have hxi0 : 0 ≤ x i := hx.1.1 i
      have hxi1 : x i ≤ 1 := hx.1.2 i
      nlinarith
    have hNegResid :
        (Finset.univ \ P).sum (fun i ↦ (c i + |c j|) * x i) ≤ 0 := by
      refine Finset.sum_nonpos ?_
      intro i hi
      have hci : c i ≤ 0 := by
        exact not_lt.mp fun hlt ↦ (Finset.mem_sdiff.mp hi).2 (by simp [P, hlt])
      have hcoef : c i + |c j| ≤ 0 := by
        have habs : |c i| = -c i := abs_of_nonpos hci
        have hji : |c j| ≤ -c i := by simpa [habs] using hj i
        linarith
      have hxi0 : 0 ≤ x i := hx.1.1 i
      nlinarith
    have hBound : c ⬝ᵥ x ≤ P.sum c - |c j| := by
      calc
        c ⬝ᵥ x =
            |c j| * (P.sum x - (Finset.univ \ P).sum x) +
              P.sum (fun i ↦ (c i - |c j|) * x i) +
              (Finset.univ \ P).sum (fun i ↦ (c i + |c j|) * x i) := by
                rw [hDecomp, hPosDecomp, hNegDecomp]
                ring
        _ ≤ |c j| * ((P.card : ℝ) - 1) + P.sum (fun i ↦ c i - |c j|) := by
              linarith
        _ = P.sum c - |c j| := by
              rw [Finset.sum_sub_distrib, Finset.sum_const]
              simp [nsmul_eq_mul]
              ring
    calc
      c ⬝ᵥ x ≤ P.sum c - |c j| := hBound
      _ = c ⬝ᵥ xopt := by simpa [hEvenP] using hOptValue.symm

/-- Helper for Theorem 4.46: the odd-set polyhedron is integral because every linear maximum is
attained by an even `0,1` vertex. -/
private lemma odd_set_polyhedron_is_integral (n : ℕ) :
    is_integral (odd_set_polyhedron n) := by
  refine
    (rational_polyhedron_is_integral_iff_linear_maxima_attained_by_integral_points
      (P := odd_set_polyhedron n) (odd_set_polyhedron_is_rational_polyhedron n)).2 ?_
  intro c z hz
  cases n with
  | zero =>
      rcases hz.1 with ⟨x, hx, hxz⟩
      refine ⟨x, ⟨hx, ?_⟩, hxz⟩
      rw [mem_integerVectors_iff_forall]
      intro i
      exact Fin.elim0 i
  | succ n =>
      classical
      obtain ⟨j, -, hj⟩ :=
        Finset.exists_min_image (Finset.univ : Finset (Fin (n + 1))) (fun i ↦ |c i|)
          Finset.univ_nonempty
      let xopt := exercise_3_4_even_parity_optimizer (-c) j
      have hxoptEven : xopt ∈ even_zero_one_vectors (n + 1) :=
        evenParityOptimizer_mem_even_zero_one_vectors (n + 1) (-c) j
      have hxopt : xopt ∈ odd_set_polyhedron (n + 1) :=
        even_zero_one_vectors_subset_odd_set_polyhedron (n + 1) hxoptEven
      have hxoptInt : xopt ∈ ℤ^(n + 1) :=
        mem_integerVectors_of_even_zero_one_vectors hxoptEven
      have hoptLe : c ⬝ᵥ xopt ≤ z := hz.2 ⟨xopt, hxopt, rfl⟩
      rcases hz.1 with ⟨x, hx, hxz⟩
      have hzLe : z ≤ c ⬝ᵥ xopt := by
        simpa [hxz] using
          dotProduct_le_evenParityOptimizer_of_mem_odd_set_polyhedron hx c j
            (fun i ↦ hj i (by simp))
      have hEq : c ⬝ᵥ xopt = z := le_antisymm hoptLe hzLe
      exact ⟨xopt, ⟨hxopt, hxoptInt⟩, hEq⟩

/-- Theorem 4.46. Let `𝒮` be the family of subsets of `N = {1, ..., n}` having odd cardinality.
Then the convex hull of the `0,1` vectors with even cardinality support is exactly the subset of
`ℝ^n` cut out by the odd-set inequalities and the box constraints `0 ≤ x_i ≤ 1`. -/
theorem convexHull_even_zero_one_vectors_eq_odd_set_polyhedron (n : ℕ) :
    convexHull ℝ (even_zero_one_vectors n) = odd_set_polyhedron n := by
  have hIntegral : is_integral (odd_set_polyhedron n) := odd_set_polyhedron_is_integral n
  rw [is_integral_iff] at hIntegral
  calc
    convexHull ℝ (even_zero_one_vectors n) =
        convexHull ℝ (odd_set_polyhedron n ∩ ℤ^n) := by
          congr 1
          ext x
          constructor
          · intro hx
            exact ⟨even_zero_one_vectors_subset_odd_set_polyhedron n hx,
              mem_integerVectors_of_even_zero_one_vectors hx⟩
          · rintro ⟨hxP, hxZ⟩
            exact mem_even_zero_one_vectors_of_mem_odd_set_polyhedron_of_integer hxP hxZ
    _ = odd_set_polyhedron n := hIntegral.symm
