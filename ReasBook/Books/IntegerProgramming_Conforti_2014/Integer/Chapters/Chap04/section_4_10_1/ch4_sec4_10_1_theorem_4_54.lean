import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_10_1.ch4_sec4_10_1_definition_4_10_1_extra_2

noncomputable section

open scoped UniqueDisjointnessMatrixNotation
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-!
Domain-style sampling for this refine pass:
* primary domain: rectangle covers of finite-support matrices in communication complexity
* source-facing matrix datum reused here: `unique_disjointness_matrix`
* core owner abstraction reused here: `rectangle_covering_number`
* supporting owner API inspected in the same domain:
  `rectangle_covering_number_eq_sInf`, `rectangle_covering_number_spec`,
  `rectangle_covering_number_le`, `unique_disjointness_matrix_apply`

This theorem is source-facing: it gives a lower bound for the rectangle covering number of the
chapter's canonical unique-disjointness matrix owner, without introducing any parallel local
wrapper around that owner.
-/

/-- Helper for Theorem 4.54: `finSuccEquivLast` is injective enough to serve as the `filterMap`
inverse that drops the last coordinate. -/
private theorem finSuccEquivLast_filterMap_injective {n : ℕ} :
    ∀ a a' : Fin (n + 1), ∀ b ∈ finSuccEquivLast a, b ∈ finSuccEquivLast a' → a = a' := by
  intro a a' b hb hb'
  have hEq : finSuccEquivLast a = some b := by
    simpa using hb
  have hEq' : finSuccEquivLast a' = some b := by
    simpa using hb'
  exact finSuccEquivLast.injective (hEq.trans hEq'.symm)

/-- Helper for Theorem 4.54: lift a subset of `Fin n` to the corresponding subset of
`Fin (n + 1)` avoiding `Fin.last n`. -/
private def liftFinset {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  s.map Fin.castSuccEmb

/-- Helper for Theorem 4.54: forget the last coordinate from a subset of `Fin (n + 1)`. -/
private def dropFinset {n : ℕ} (s : Finset (Fin (n + 1))) : Finset (Fin n) :=
  s.filterMap finSuccEquivLast finSuccEquivLast_filterMap_injective

/-- Helper for Theorem 4.54: add the last coordinate to a lifted subset. -/
private def insertLast {n : ℕ} (s : Finset (Fin n)) : Finset (Fin (n + 1)) :=
  insert (Fin.last n) (liftFinset s)

/-- Helper for Theorem 4.54: the disjoint pairs drawn from row family `A` and column family `B`. -/
private def disjointPairs {n : ℕ} (A B : Finset (Finset (Fin n))) :
    Finset (Finset (Fin n) × Finset (Fin n)) :=
  (A.product B).filter (fun p ↦ Disjoint p.1 p.2)

/-- Helper for Theorem 4.54: all disjoint row/column index pairs for `U^n`. -/
private def allDisjointPairs (n : ℕ) : Finset (Finset (Fin n) × Finset (Fin n)) :=
  disjointPairs Finset.univ Finset.univ

/-- Helper for Theorem 4.54: lifting preserves membership by `Fin.castSucc`. -/
@[simp] private theorem mem_liftFinset {n : ℕ} {s : Finset (Fin n)} {i : Fin n} :
    i.castSucc ∈ liftFinset s ↔ i ∈ s := by
  simpa [liftFinset] using (Finset.mem_map' Fin.castSuccEmb (a := i) (s := s))

/-- Helper for Theorem 4.54: dropping the last coordinate reverses `castSucc`. -/
@[simp] private theorem mem_dropFinset {n : ℕ} {s : Finset (Fin (n + 1))} {i : Fin n} :
    i ∈ dropFinset s ↔ i.castSucc ∈ s := by
  rw [dropFinset, Finset.mem_filterMap]
  constructor
  · rintro ⟨a, ha, hsome⟩
    have ha' : a = i.castSucc := finSuccEquivLast.injective <| by
      simpa [finSuccEquivLast_castSucc] using hsome
    simpa [ha'] using ha
  · intro hi
    exact ⟨i.castSucc, hi, finSuccEquivLast_castSucc i⟩

/-- Helper for Theorem 4.54: the lifted image never contains the last coordinate. -/
@[simp] private theorem last_not_mem_liftFinset {n : ℕ} {s : Finset (Fin n)} :
    Fin.last n ∉ liftFinset s := by
  simp [liftFinset]

/-- Helper for Theorem 4.54: dropping after lifting is the identity. -/
@[simp] private theorem dropFinset_liftFinset {n : ℕ} (s : Finset (Fin n)) :
    dropFinset (liftFinset s) = s := by
  ext i
  simp

/-- Helper for Theorem 4.54: dropping after inserting the last coordinate is the identity. -/
@[simp] private theorem dropFinset_insertLast {n : ℕ} (s : Finset (Fin n)) :
    dropFinset (insertLast s) = s := by
  ext i
  simp [insertLast]

/-- Helper for Theorem 4.54: lifting after dropping recovers a set missing the last coordinate. -/
private theorem liftFinset_dropFinset_of_last_not_mem {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : Fin.last n ∉ s) :
    liftFinset (dropFinset s) = s := by
  ext i
  by_cases hi : i = Fin.last n
  · subst hi
    simp [h]
  · have hi' : i ∈ liftFinset (dropFinset s) ↔ i ∈ s := by
      simpa [Fin.castSucc_castPred i hi] using
        (mem_liftFinset (s := dropFinset s) (i := i.castPred hi)).trans
          (mem_dropFinset (s := s) (i := i.castPred hi))
    exact hi'

/-- Helper for Theorem 4.54: adding back the last coordinate recovers a set that contains it. -/
private theorem insertLast_dropFinset_of_last_mem {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : Fin.last n ∈ s) :
    insertLast (dropFinset s) = s := by
  ext i
  by_cases hi : i = Fin.last n
  · subst hi
    simp [insertLast, h]
  · have hi' : i ∈ insertLast (dropFinset s) ↔ i ∈ s := by
      simpa [insertLast, hi, Fin.castSucc_castPred i hi] using
        (mem_liftFinset (s := dropFinset s) (i := i.castPred hi)).trans
          (mem_dropFinset (s := s) (i := i.castPred hi))
    exact hi'

/-- Helper for Theorem 4.54: dropping commutes with intersection. -/
@[simp] private theorem dropFinset_inter {n : ℕ} (a b : Finset (Fin (n + 1))) :
    dropFinset (a ∩ b) = dropFinset a ∩ dropFinset b := by
  ext i
  simp [and_left_comm, and_assoc]

/-- Helper for Theorem 4.54: if the last coordinate is absent then dropping preserves cardinality. -/
private theorem card_dropFinset_eq {n : ℕ} {s : Finset (Fin (n + 1))}
    (h : Fin.last n ∉ s) :
    (dropFinset s).card = s.card := by
  calc
    (dropFinset s).card = (liftFinset (dropFinset s)).card := by
      simpa [liftFinset] using (Finset.card_map (f := Fin.castSuccEmb) (s := dropFinset s)).symm
    _ = s.card := by rw [liftFinset_dropFinset_of_last_not_mem h]

/-- Helper for Theorem 4.54: if the right set omits the last coordinate then dropping preserves
intersection cardinality. -/
private theorem inter_card_dropFinset_eq_of_right_last_not_mem {n : ℕ}
    {a b : Finset (Fin (n + 1))} (hb : Fin.last n ∉ b) :
    (dropFinset a ∩ dropFinset b).card = (a ∩ b).card := by
  rw [← dropFinset_inter]
  exact card_dropFinset_eq (by
    intro hmem
    exact hb <| (Finset.mem_inter.mp hmem).2)

/-- Helper for Theorem 4.54: if the left set omits the last coordinate then dropping preserves
intersection cardinality. -/
private theorem inter_card_dropFinset_eq_of_left_last_not_mem {n : ℕ}
    {a b : Finset (Fin (n + 1))} (ha : Fin.last n ∉ a) :
    (dropFinset a ∩ dropFinset b).card = (a ∩ b).card := by
  rw [Finset.inter_comm, Finset.inter_comm a b]
  exact inter_card_dropFinset_eq_of_right_last_not_mem ha

/-- Helper for Theorem 4.54: support membership in `U^n` is exactly the non-singleton
intersection condition. -/
private theorem uniqueDisjointnessMatrix_memSupport_iff {n : ℕ}
    {a b : Finset (Fin n)} :
    (a, b) ∈ matrix_support (U^n) ↔ (a ∩ b).card ≠ 1 := by
  -- Rewrite support membership to the entrywise zero test from the matrix definition.
  rw [mem_matrix_support_iff, Ne, unique_disjointness_matrix_eq_zero_iff]

/-- Helper for Theorem 4.54: disjoint pairs automatically lie in the support of `U^n`. -/
private theorem disjoint_memSupport_uniqueDisjointnessMatrix {n : ℕ}
    {a b : Finset (Fin n)} (h : Disjoint a b) :
    (a, b) ∈ matrix_support (U^n) := by
  -- A disjoint pair has intersection cardinality `0`, hence certainly not `1`.
  rw [uniqueDisjointnessMatrix_memSupport_iff]
  have hcard : (a ∩ b).card = 0 := by
    simpa using congrArg Finset.card h.eq_bot
  omega

/-- Helper for Theorem 4.54: membership in `disjointPairs` expands to row membership, column
membership, and disjointness. -/
private theorem mem_disjointPairs_iff {n : ℕ} {A B : Finset (Finset (Fin n))}
    {a : Finset (Fin n)} {b : Finset (Fin n)} :
    (a, b) ∈ disjointPairs A B ↔ a ∈ A ∧ b ∈ B ∧ Disjoint a b := by
  simp [disjointPairs, and_left_comm, and_assoc]

/-- Helper for Theorem 4.54: `disjointPairs` distributes over a union of row families. -/
private theorem disjointPairs_union_left {n : ℕ}
    (A₁ A₂ B : Finset (Finset (Fin n))) :
    disjointPairs (A₁ ∪ A₂) B = disjointPairs A₁ B ∪ disjointPairs A₂ B := by
  ext p
  rcases p with ⟨a, b⟩
  constructor
  · intro hp
    have hp' := (mem_disjointPairs_iff).1 hp
    have haUnion : a ∈ A₁ ∪ A₂ := hp'.1
    rw [Finset.mem_union] at haUnion
    rcases haUnion with ha | ha
    · exact Finset.mem_union.mpr <| Or.inl <| (mem_disjointPairs_iff).2 ⟨ha, hp'.2.1, hp'.2.2⟩
    · exact Finset.mem_union.mpr <| Or.inr <| (mem_disjointPairs_iff).2 ⟨ha, hp'.2.1, hp'.2.2⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mem_disjointPairs_iff).2 <| by
        rw [mem_disjointPairs_iff] at hp
        exact ⟨Finset.mem_union.mpr <| Or.inl hp.1, hp.2.1, hp.2.2⟩
    · exact (mem_disjointPairs_iff).2 <| by
        rw [mem_disjointPairs_iff] at hp
        exact ⟨Finset.mem_union.mpr <| Or.inr hp.1, hp.2.1, hp.2.2⟩

/-- Helper for Theorem 4.54: `disjointPairs` distributes over a union of column families. -/
private theorem disjointPairs_union_right {n : ℕ}
    (A B₁ B₂ : Finset (Finset (Fin n))) :
    disjointPairs A (B₁ ∪ B₂) = disjointPairs A B₁ ∪ disjointPairs A B₂ := by
  ext p
  rcases p with ⟨a, b⟩
  constructor
  · intro hp
    have hp' := (mem_disjointPairs_iff).1 hp
    have hbUnion : b ∈ B₁ ∪ B₂ := hp'.2.1
    rw [Finset.mem_union] at hbUnion
    rcases hbUnion with hb | hb
    · exact Finset.mem_union.mpr <| Or.inl <| (mem_disjointPairs_iff).2 ⟨hp'.1, hb, hp'.2.2⟩
    · exact Finset.mem_union.mpr <| Or.inr <| (mem_disjointPairs_iff).2 ⟨hp'.1, hb, hp'.2.2⟩
  · intro hp
    rcases Finset.mem_union.mp hp with hp | hp
    · exact (mem_disjointPairs_iff).2 <| by
        rw [mem_disjointPairs_iff] at hp
        exact ⟨hp.1, Finset.mem_union.mpr <| Or.inl hp.2.1, hp.2.2⟩
    · exact (mem_disjointPairs_iff).2 <| by
        rw [mem_disjointPairs_iff] at hp
        exact ⟨hp.1, Finset.mem_union.mpr <| Or.inr hp.2.1, hp.2.2⟩

/-- Helper for Theorem 4.54: dropping preserves disjointness. -/
private theorem Disjoint.dropFinset {n : ℕ}
    {a b : Finset (Fin (n + 1))} (h : Disjoint a b) :
    Disjoint (dropFinset a) (dropFinset b) := by
  rw [Finset.disjoint_left] at *
  intro i hiA hiB
  exact h (by simpa using hiA) (by simpa using hiB)

/-- Helper for Theorem 4.54: lifting preserves disjointness. -/
private theorem disjoint_liftFinset_iff {n : ℕ}
    {a b : Finset (Fin n)} :
    Disjoint (liftFinset a) (liftFinset b) ↔ Disjoint a b := by
  constructor
  · intro h
    rw [Finset.disjoint_left] at *
    intro i hiA hiB
    have hiA' : i.castSucc ∈ liftFinset a := by
      simpa using hiA
    have hiB' : i.castSucc ∈ liftFinset b := by
      simpa using hiB
    exact h hiA' hiB'
  · intro h
    rw [Finset.disjoint_left] at *
    intro i hiA hiB
    rcases (Finset.mem_map.mp hiA) with ⟨j, hj, rfl⟩
    rcases (Finset.mem_map.mp hiB) with ⟨k, hk, hkEq⟩
    have hk' : k = j := by simpa using hkEq
    subst hk'
    exact h hj hk

/-- Helper for Theorem 4.54: inserting the last coordinate on the left preserves disjointness
against a lifted right set. -/
private theorem disjoint_insertLast_liftFinset_iff {n : ℕ}
    {a b : Finset (Fin n)} :
    Disjoint (insertLast a) (liftFinset b) ↔ Disjoint a b := by
  constructor
  · intro h
    rw [Finset.disjoint_left] at *
    intro i hiA hiB
    have hiA' : i.castSucc ∈ insertLast a := by
      simp [insertLast, hiA]
    have hiB' : i.castSucc ∈ liftFinset b := by
      simpa using hiB
    exact h hiA' hiB'
  · intro h
    rw [Finset.disjoint_left] at *
    intro i hiA hiB
    rcases Finset.mem_insert.mp hiA with rfl | hiA
    · exact last_not_mem_liftFinset hiB
    · rcases (Finset.mem_map.mp hiA) with ⟨j, hj, rfl⟩
      rcases (Finset.mem_map.mp hiB) with ⟨k, hk, hkEq⟩
      have hk' : k = j := by simpa using hkEq
      subst hk'
      exact h hj hk

/-- Helper for Theorem 4.54: inserting the last coordinate on the right preserves disjointness
against a lifted left set. -/
private theorem disjoint_liftFinset_insertLast_iff {n : ℕ}
    {a b : Finset (Fin n)} :
    Disjoint (liftFinset a) (insertLast b) ↔ Disjoint a b := by
  rw [disjoint_comm, disjoint_insertLast_liftFinset_iff, disjoint_comm]

/-- Helper for Theorem 4.54: add the last coordinate on the left of a disjoint pair. -/
private def leftPair {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin (n + 1)) × Finset (Fin (n + 1)) :=
  (insertLast p.1, liftFinset p.2)

/-- Helper for Theorem 4.54: add the last coordinate on the right of a disjoint pair. -/
private def rightPair {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin (n + 1)) × Finset (Fin (n + 1)) :=
  (liftFinset p.1, insertLast p.2)

/-- Helper for Theorem 4.54: lift a disjoint pair without using the last coordinate. -/
private def centerPair {n : ℕ} (p : Finset (Fin n) × Finset (Fin n)) :
    Finset (Fin (n + 1)) × Finset (Fin (n + 1)) :=
  (liftFinset p.1, liftFinset p.2)

/-- Helper for Theorem 4.54: the left lift of a pair is injective. -/
private theorem leftPair_injective {n : ℕ} :
    Function.Injective (leftPair (n := n)) := by
  intro p q hpq
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  simp [leftPair] at hpq
  rcases hpq with ⟨hfst, hsnd⟩
  have ha : a = a' := by
    have hdrop := congrArg dropFinset hfst
    simpa using hdrop
  have hb : b = b' := by
    have hdrop := congrArg dropFinset hsnd
    simpa using hdrop
  simp [ha, hb]

/-- Helper for Theorem 4.54: the right lift of a pair is injective. -/
private theorem rightPair_injective {n : ℕ} :
    Function.Injective (rightPair (n := n)) := by
  intro p q hpq
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  simp [rightPair] at hpq
  rcases hpq with ⟨hfst, hsnd⟩
  have ha : a = a' := by
    have hdrop := congrArg dropFinset hfst
    simpa using hdrop
  have hb : b = b' := by
    have hdrop := congrArg dropFinset hsnd
    simpa using hdrop
  simp [ha, hb]

/-- Helper for Theorem 4.54: the centered lift of a pair is injective. -/
private theorem centerPair_injective {n : ℕ} :
    Function.Injective (centerPair (n := n)) := by
  intro p q hpq
  rcases p with ⟨a, b⟩
  rcases q with ⟨a', b'⟩
  simp [centerPair] at hpq
  rcases hpq with ⟨hfst, hsnd⟩
  have ha : a = a' := by
    simpa using congrArg dropFinset hfst
  have hb : b = b' := by
    simpa using congrArg dropFinset hsnd
  simp [ha, hb]

/-- Helper for Theorem 4.54: drop the last coordinate from both components of a pair. -/
private def dropPair {n : ℕ} (p : Finset (Fin (n + 1)) × Finset (Fin (n + 1))) :
    Finset (Fin n) × Finset (Fin n) :=
  (dropFinset p.1, dropFinset p.2)

/-- Helper for Theorem 4.54: a pair whose left component contains the last coordinate is recovered
as a `leftPair` after dropping. -/
private theorem leftPair_dropPair_of_last_mem {n : ℕ}
    {p : Finset (Fin (n + 1)) × Finset (Fin (n + 1))}
    (hLeft : Fin.last n ∈ p.1) (hRight : Fin.last n ∉ p.2) :
    leftPair (dropPair p) = p := by
  rcases p with ⟨a, b⟩
  -- Recover the original pair componentwise from the drop-and-reinsert API.
  simp [dropPair, leftPair, insertLast_dropFinset_of_last_mem hLeft,
    liftFinset_dropFinset_of_last_not_mem hRight]

/-- Helper for Theorem 4.54: a pair whose right component contains the last coordinate is recovered
as a `rightPair` after dropping. -/
private theorem rightPair_dropPair_of_last_mem {n : ℕ}
    {p : Finset (Fin (n + 1)) × Finset (Fin (n + 1))}
    (hLeft : Fin.last n ∉ p.1) (hRight : Fin.last n ∈ p.2) :
    rightPair (dropPair p) = p := by
  rcases p with ⟨a, b⟩
  -- Recover the original pair componentwise from the drop-and-reinsert API.
  simp [dropPair, rightPair, liftFinset_dropFinset_of_last_not_mem hLeft,
    insertLast_dropFinset_of_last_mem hRight]

/-- Helper for Theorem 4.54: a pair omitting the last coordinate on both sides is recovered as a
`centerPair` after dropping. -/
private theorem centerPair_dropPair_of_last_not_mem {n : ℕ}
    {p : Finset (Fin (n + 1)) × Finset (Fin (n + 1))}
    (hLeft : Fin.last n ∉ p.1) (hRight : Fin.last n ∉ p.2) :
    centerPair (dropPair p) = p := by
  rcases p with ⟨a, b⟩
  -- When the last coordinate is absent from both sides, lifting the dropped pair recovers it.
  simp [dropPair, centerPair, liftFinset_dropFinset_of_last_not_mem hLeft,
    liftFinset_dropFinset_of_last_not_mem hRight]

/-- Helper for Theorem 4.54: adding the last coordinate to both sides of a disjoint smaller pair
creates an intersection of cardinality `1`. -/
private theorem insertLast_inter_insertLast_card_of_disjoint {n : ℕ}
    {a b : Finset (Fin n)} (h : Disjoint a b) :
    (insertLast a ∩ insertLast b).card = 1 := by
  -- Isolate the new common point as the unique copy of `Fin.last n`.
  have hEq :
      insertLast a ∩ insertLast b = insert (Fin.last n) (liftFinset a ∩ liftFinset b) := by
    ext i
    by_cases hi : i = Fin.last n
    · subst hi
      simp [insertLast]
    · simp [insertLast, hi, and_left_comm, and_assoc]
  have hLiftDisjoint : Disjoint (liftFinset a) (liftFinset b) := (disjoint_liftFinset_iff).2 h
  have hCardZero : (liftFinset a ∩ liftFinset b).card = 0 := by
    simpa using congrArg Finset.card hLiftDisjoint.eq_bot
  calc
    (insertLast a ∩ insertLast b).card
        = (insert (Fin.last n) (liftFinset a ∩ liftFinset b)).card := by rw [hEq]
    _ = (liftFinset a ∩ liftFinset b).card + 1 := by
      simp [last_not_mem_liftFinset]
    _ = 1 := by simp [hCardZero]

/-- Helper for Theorem 4.54: decode a `Fin 3`-valued function as the left/right/neither choice
for a disjoint pair of subsets. -/
private def decodeDisjointPair {n : ℕ} (f : Fin n → Fin 3) :
    Finset (Fin n) × Finset (Fin n) :=
  (Finset.univ.filter (fun i ↦ f i = 0), Finset.univ.filter (fun i ↦ f i = 1))

/-- Helper for Theorem 4.54: the decoder from `Fin n → Fin 3` always produces a disjoint pair. -/
private theorem decodeDisjointPair_disjoint {n : ℕ} (f : Fin n → Fin 3) :
    Disjoint (decodeDisjointPair f).1 (decodeDisjointPair f).2 := by
  -- A coordinate cannot be coded simultaneously as both the left and the right choice.
  rw [Finset.disjoint_left]
  intro i hiLeft hiRight
  simp [decodeDisjointPair] at hiLeft hiRight
  rw [hiLeft] at hiRight
  norm_num at hiRight

/-- Helper for Theorem 4.54: disjoint pairs of subsets of `Fin n` are equivalent to
three-way choices on each coordinate. -/
private def disjointPairSubtypeEquivFinThreeFunctions (n : ℕ) :
    {p : Finset (Fin n) × Finset (Fin n) // Disjoint p.1 p.2} ≃ (Fin n → Fin 3) := by
  refine
    { toFun := fun p i ↦ if i ∈ p.1.1 then 0 else if i ∈ p.1.2 then 1 else 2
      invFun := fun f ↦ ⟨decodeDisjointPair f, decodeDisjointPair_disjoint f⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro p
    rcases p with ⟨⟨a, b⟩, hab⟩
    change Disjoint a b at hab
    have hab' := Finset.disjoint_left.mp hab
    apply Subtype.ext
    -- Reconstruct the original pair by checking whether each coordinate was coded left, right,
    -- or neither.
    apply Prod.ext
    · ext i
      by_cases hiA : i ∈ a
      · have hiB : i ∉ b := by
          intro hiB
          exact hab' hiA hiB
        simp [decodeDisjointPair, hiA, hiB]
      · by_cases hiB : i ∈ b
        · simp [decodeDisjointPair, hiA, hiB]
        · simp [decodeDisjointPair, hiA, hiB]
    · ext i
      by_cases hiA : i ∈ a
      · have hiB : i ∉ b := by
          intro hiB
          exact hab' hiA hiB
        simp [decodeDisjointPair, hiA, hiB]
      · by_cases hiB : i ∈ b
        · simp [decodeDisjointPair, hiA, hiB]
        · simp [decodeDisjointPair, hiA, hiB]
  · intro f
    -- Every `Fin 3` code is one of the three constructors used by the decoder.
    ext i
    have hcases : (f i).1 = 0 ∨ (f i).1 = 1 ∨ (f i).1 = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · have h : f i = 0 := Fin.ext h0
      simp [decodeDisjointPair, h]
    · have h : f i = 1 := Fin.ext h1
      simp [decodeDisjointPair, h]
    · have h : f i = 2 := Fin.ext h2
      simp [decodeDisjointPair, h]

/-- Helper for Theorem 4.54: there are exactly `3^n` disjoint pairs of subsets of `Fin n`. -/
private theorem allDisjointPairs_card : ∀ n : ℕ, (allDisjointPairs n).card = 3 ^ n
  := by
    intro n
    -- Replace the earlier last-coordinate decomposition by the canonical `Fin 3` coding.
    rw [← Fintype.card_ofFinset
      (p := {p : Finset (Fin n) × Finset (Fin n) | Disjoint p.1 p.2})
      (s := allDisjointPairs n)]
    · calc
        Fintype.card {p : Finset (Fin n) × Finset (Fin n) // Disjoint p.1 p.2}
            = Fintype.card (Fin n → Fin 3) :=
              Fintype.card_congr (disjointPairSubtypeEquivFinThreeFunctions n)
        _ = 3 ^ n := by
          simpa using (Fintype.card_fun (α := Fin n) (β := Fin 3))
    · intro p
      rcases p with ⟨a, b⟩
      simp [allDisjointPairs, disjointPairs]

/-- Helper for Theorem 4.54: any valid family of disjoint row/column pairs on `Fin n` has
cardinality at most `2^n`. -/
private theorem validDisjointPairFamily_card_le :
    ∀ n : ℕ, ∀ D : Finset (Finset (Fin n) × Finset (Fin n)),
      (∀ p ∈ D, Disjoint p.1 p.2) →
      (∀ a ∈ D.image Prod.fst, ∀ b ∈ D.image Prod.snd, (a ∩ b).card ≠ 1) →
      D.card ≤ 2 ^ n := by
  intro n
  induction n with
  | zero =>
      intro D hDisjoint hCross
      -- Over `Fin 0` there is only one possible pair, so every family has size at most `1`.
      simpa using (Finset.card_le_univ D)
  | succ n ih =>
      intro D hDisjoint hCross
      let D1' := D.filter
        (fun p ↦ Fin.last n ∈ p.1 ∨ (Fin.last n ∉ p.2 ∧ leftPair (dropPair p) ∉ D))
      let D2' := D.filter
        (fun p ↦ Fin.last n ∈ p.2 ∨ (Fin.last n ∉ p.1 ∧ rightPair (dropPair p) ∉ D))
      let D1 := D1'.image dropPair
      let D2 := D2'.image dropPair
      have hD1Subset : D1' ⊆ D := by
        intro p hp
        exact (by simpa [D1'] using hp : p ∈ D ∧
          (Fin.last n ∈ p.1 ∨ (Fin.last n ∉ p.2 ∧ leftPair (dropPair p) ∉ D))).1
      have hD2Subset : D2' ⊆ D := by
        intro p hp
        exact (by simpa [D2'] using hp : p ∈ D ∧
          (Fin.last n ∈ p.2 ∨ (Fin.last n ∉ p.1 ∧ rightPair (dropPair p) ∉ D))).1
      have hD1RightNot : ∀ p ∈ D1', Fin.last n ∉ p.2 := by
        intro p hp
        have hp' : p ∈ D ∧
            (Fin.last n ∈ p.1 ∨ (Fin.last n ∉ p.2 ∧ leftPair (dropPair p) ∉ D)) := by
          simpa [D1'] using hp
        rcases hp'.2 with hLeft | hSecond
        · have hpDisjoint := hDisjoint p hp'.1
          rw [Finset.disjoint_left] at hpDisjoint
          exact fun hRight ↦ hpDisjoint hLeft hRight
        · exact hSecond.1
      have hD2LeftNot : ∀ p ∈ D2', Fin.last n ∉ p.1 := by
        intro p hp
        have hp' : p ∈ D ∧
            (Fin.last n ∈ p.2 ∨ (Fin.last n ∉ p.1 ∧ rightPair (dropPair p) ∉ D)) := by
          simpa [D2'] using hp
        rcases hp'.2 with hRight | hSecond
        · have hpDisjoint := hDisjoint p hp'.1
          rw [Finset.disjoint_left] at hpDisjoint
          exact fun hLeft ↦ hpDisjoint hLeft hRight
        · exact hSecond.1
      have hCover : D ⊆ D1' ∪ D2' := by
        intro p hp
        have hpDisjoint := hDisjoint p hp
        have hDropDisjoint : Disjoint (dropPair p).1 (dropPair p).2 := hpDisjoint.dropFinset
        by_cases hLeft : Fin.last n ∈ p.1
        · exact Finset.mem_union.mpr <| Or.inl <| by simpa [D1', hp, hLeft]
        · by_cases hRight : Fin.last n ∈ p.2
          · exact Finset.mem_union.mpr <| Or.inr <| by simpa [D2', hp, hLeft, hRight]
          · by_cases hLeftLift : leftPair (dropPair p) ∈ D
            · by_cases hRightLift : rightPair (dropPair p) ∈ D
              · have hRow : (leftPair (dropPair p)).1 ∈ D.image Prod.fst := by
                  exact Finset.mem_image.mpr ⟨leftPair (dropPair p), hLeftLift, rfl⟩
                have hCol : (rightPair (dropPair p)).2 ∈ D.image Prod.snd := by
                  exact Finset.mem_image.mpr ⟨rightPair (dropPair p), hRightLift, rfl⟩
                have hCard :
                    (((leftPair (dropPair p)).1 ∩ (rightPair (dropPair p)).2).card) = 1 := by
                  simpa [leftPair, rightPair] using
                    insertLast_inter_insertLast_card_of_disjoint hDropDisjoint
                exact False.elim ((hCross _ hRow _ hCol) hCard)
              · exact Finset.mem_union.mpr <| Or.inr <| by
                  simpa [D2', hp, hLeft, hRight, hRightLift]
            · exact Finset.mem_union.mpr <| Or.inl <| by
                simpa [D1', hp, hLeft, hRight, hLeftLift]
      have hD1Inj :
          Set.InjOn dropPair
            ((↑D1' : Set (Finset (Fin (n + 1)) × Finset (Fin (n + 1))))) := by
        intro p hp q hq hEq
        have hp' : p ∈ D ∧
            (Fin.last n ∈ p.1 ∨ (Fin.last n ∉ p.2 ∧ leftPair (dropPair p) ∉ D)) := by
          simpa [D1'] using hp
        have hq' : q ∈ D ∧
            (Fin.last n ∈ q.1 ∨ (Fin.last n ∉ q.2 ∧ leftPair (dropPair q) ∉ D)) := by
          simpa [D1'] using hq
        have hpRightNot : Fin.last n ∉ p.2 := hD1RightNot p hp
        have hqRightNot : Fin.last n ∉ q.2 := hD1RightNot q hq
        by_cases hpLeft : Fin.last n ∈ p.1
        · have hpRec : leftPair (dropPair p) = p :=
            leftPair_dropPair_of_last_mem hpLeft hpRightNot
          have hqLeft : Fin.last n ∈ q.1 := by
            by_contra hqLeftNot
            have hqSecond : Fin.last n ∉ q.2 ∧ leftPair (dropPair q) ∉ D := by
              rcases hq'.2 with hqLeft | hqSecond
              · exact False.elim (hqLeftNot hqLeft)
              · exact hqSecond
            have hpEqLeft : leftPair (dropPair q) = p := by
              calc
                leftPair (dropPair q) = leftPair (dropPair p) := by rw [hEq]
                _ = p := hpRec
            have hpIn : leftPair (dropPair q) ∈ D := by
              simpa [hpEqLeft] using hp'.1
            exact hqSecond.2 hpIn
          have hqRec : leftPair (dropPair q) = q :=
            leftPair_dropPair_of_last_mem hqLeft hqRightNot
          calc
            p = leftPair (dropPair p) := hpRec.symm
            _ = leftPair (dropPair q) := by rw [hEq]
            _ = q := hqRec
        · have hpSecond : Fin.last n ∉ p.2 ∧ leftPair (dropPair p) ∉ D := by
            rcases hp'.2 with hpLeft' | hpSecond
            · exact False.elim (hpLeft hpLeft')
            · exact hpSecond
          have hpRec : centerPair (dropPair p) = p :=
            centerPair_dropPair_of_last_not_mem hpLeft hpRightNot
          by_cases hqLeft : Fin.last n ∈ q.1
          · have hqRec : leftPair (dropPair q) = q :=
              leftPair_dropPair_of_last_mem hqLeft hqRightNot
            have hqEqLeft : leftPair (dropPair p) = q := by
              calc
                leftPair (dropPair p) = leftPair (dropPair q) := by rw [hEq]
                _ = q := hqRec
            have hqIn : leftPair (dropPair p) ∈ D := by
              simpa [hqEqLeft] using hq'.1
            exact False.elim (hpSecond.2 hqIn)
          · have hqRec : centerPair (dropPair q) = q :=
              centerPair_dropPair_of_last_not_mem hqLeft hqRightNot
            calc
              p = centerPair (dropPair p) := hpRec.symm
              _ = centerPair (dropPair q) := by rw [hEq]
              _ = q := hqRec
      have hD2Inj :
          Set.InjOn dropPair
            ((↑D2' : Set (Finset (Fin (n + 1)) × Finset (Fin (n + 1))))) := by
        intro p hp q hq hEq
        have hp' : p ∈ D ∧
            (Fin.last n ∈ p.2 ∨ (Fin.last n ∉ p.1 ∧ rightPair (dropPair p) ∉ D)) := by
          simpa [D2'] using hp
        have hq' : q ∈ D ∧
            (Fin.last n ∈ q.2 ∨ (Fin.last n ∉ q.1 ∧ rightPair (dropPair q) ∉ D)) := by
          simpa [D2'] using hq
        have hpLeftNot : Fin.last n ∉ p.1 := hD2LeftNot p hp
        have hqLeftNot : Fin.last n ∉ q.1 := hD2LeftNot q hq
        by_cases hpRight : Fin.last n ∈ p.2
        · have hpRec : rightPair (dropPair p) = p :=
            rightPair_dropPair_of_last_mem hpLeftNot hpRight
          have hqRight : Fin.last n ∈ q.2 := by
            by_contra hqRightNot
            have hqSecond : Fin.last n ∉ q.1 ∧ rightPair (dropPair q) ∉ D := by
              rcases hq'.2 with hqRight | hqSecond
              · exact False.elim (hqRightNot hqRight)
              · exact hqSecond
            have hpEqRight : rightPair (dropPair q) = p := by
              calc
                rightPair (dropPair q) = rightPair (dropPair p) := by rw [hEq]
                _ = p := hpRec
            have hpIn : rightPair (dropPair q) ∈ D := by
              simpa [hpEqRight] using hp'.1
            exact hqSecond.2 hpIn
          have hqRec : rightPair (dropPair q) = q :=
            rightPair_dropPair_of_last_mem hqLeftNot hqRight
          calc
            p = rightPair (dropPair p) := hpRec.symm
            _ = rightPair (dropPair q) := by rw [hEq]
            _ = q := hqRec
        · have hpSecond : Fin.last n ∉ p.1 ∧ rightPair (dropPair p) ∉ D := by
            rcases hp'.2 with hpRight' | hpSecond
            · exact False.elim (hpRight hpRight')
            · exact hpSecond
          have hpRec : centerPair (dropPair p) = p :=
            centerPair_dropPair_of_last_not_mem hpLeftNot hpRight
          by_cases hqRight : Fin.last n ∈ q.2
          · have hqRec : rightPair (dropPair q) = q :=
              rightPair_dropPair_of_last_mem hqLeftNot hqRight
            have hqEqRight : rightPair (dropPair p) = q := by
              calc
                rightPair (dropPair p) = rightPair (dropPair q) := by rw [hEq]
                _ = q := hqRec
            have hqIn : rightPair (dropPair p) ∈ D := by
              simpa [hqEqRight] using hq'.1
            exact False.elim (hpSecond.2 hqIn)
          · have hqRec : centerPair (dropPair q) = q :=
              centerPair_dropPair_of_last_not_mem hqLeftNot hqRight
            calc
              p = centerPair (dropPair p) := hpRec.symm
              _ = centerPair (dropPair q) := by rw [hEq]
              _ = q := hqRec
      have hD1Card : D1'.card = D1.card := by
        simpa [D1] using (Finset.card_image_of_injOn (s := D1') (f := dropPair) hD1Inj).symm
      have hD2Card : D2'.card = D2.card := by
        simpa [D2] using (Finset.card_image_of_injOn (s := D2') (f := dropPair) hD2Inj).symm
      have hD1Disjoint : ∀ p ∈ D1, Disjoint p.1 p.2 := by
        intro p hp
        have hp' : p ∈ D1'.image dropPair := by simpa [D1] using hp
        rcases Finset.mem_image.mp hp' with ⟨q, hq, rfl⟩
        exact (hDisjoint q (hD1Subset hq)).dropFinset
      have hD2Disjoint : ∀ p ∈ D2, Disjoint p.1 p.2 := by
        intro p hp
        have hp' : p ∈ D2'.image dropPair := by simpa [D2] using hp
        rcases Finset.mem_image.mp hp' with ⟨q, hq, rfl⟩
        exact (hDisjoint q (hD2Subset hq)).dropFinset
      have hD1Cross :
          ∀ a ∈ D1.image Prod.fst, ∀ b ∈ D1.image Prod.snd, (a ∩ b).card ≠ 1 := by
        intro a ha b hb
        rcases Finset.mem_image.mp ha with ⟨r, hrD1, rfl⟩
        rcases Finset.mem_image.mp hb with ⟨s, hsD1, rfl⟩
        have hr' : r ∈ D1'.image dropPair := by simpa [D1] using hrD1
        have hs' : s ∈ D1'.image dropPair := by simpa [D1] using hsD1
        rcases Finset.mem_image.mp hr' with ⟨p, hp, hpEq⟩
        rcases Finset.mem_image.mp hs' with ⟨q, hq, hqEq⟩
        have hpRow : p.1 ∈ D.image Prod.fst := Finset.mem_image.mpr ⟨p, hD1Subset hp, rfl⟩
        have hqCol : q.2 ∈ D.image Prod.snd := Finset.mem_image.mpr ⟨q, hD1Subset hq, rfl⟩
        have hOrig : (p.1 ∩ q.2).card ≠ 1 := hCross _ hpRow _ hqCol
        have hqRightNot : Fin.last n ∉ q.2 := hD1RightNot q hq
        have hCardEq : (r.1 ∩ s.2).card = (p.1 ∩ q.2).card := by
          have hpFst : r.1 = dropFinset p.1 := by
            simpa [dropPair] using (congrArg Prod.fst hpEq).symm
          have hqSnd : s.2 = dropFinset q.2 := by
            simpa [dropPair] using (congrArg Prod.snd hqEq).symm
          calc
            (r.1 ∩ s.2).card = (dropFinset p.1 ∩ dropFinset q.2).card := by rw [hpFst, hqSnd]
            _ = (p.1 ∩ q.2).card :=
              inter_card_dropFinset_eq_of_right_last_not_mem hqRightNot
        exact fun hOne ↦ hOrig (hCardEq.symm.trans hOne)
      have hD2Cross :
          ∀ a ∈ D2.image Prod.fst, ∀ b ∈ D2.image Prod.snd, (a ∩ b).card ≠ 1 := by
        intro a ha b hb
        rcases Finset.mem_image.mp ha with ⟨r, hrD2, rfl⟩
        rcases Finset.mem_image.mp hb with ⟨s, hsD2, rfl⟩
        have hr' : r ∈ D2'.image dropPair := by simpa [D2] using hrD2
        have hs' : s ∈ D2'.image dropPair := by simpa [D2] using hsD2
        rcases Finset.mem_image.mp hr' with ⟨p, hp, hpEq⟩
        rcases Finset.mem_image.mp hs' with ⟨q, hq, hqEq⟩
        have hpRow : p.1 ∈ D.image Prod.fst := Finset.mem_image.mpr ⟨p, hD2Subset hp, rfl⟩
        have hqCol : q.2 ∈ D.image Prod.snd := Finset.mem_image.mpr ⟨q, hD2Subset hq, rfl⟩
        have hOrig : (p.1 ∩ q.2).card ≠ 1 := hCross _ hpRow _ hqCol
        have hpLeftNot : Fin.last n ∉ p.1 := hD2LeftNot p hp
        have hCardEq : (r.1 ∩ s.2).card = (p.1 ∩ q.2).card := by
          have hpFst : r.1 = dropFinset p.1 := by
            simpa [dropPair] using (congrArg Prod.fst hpEq).symm
          have hqSnd : s.2 = dropFinset q.2 := by
            simpa [dropPair] using (congrArg Prod.snd hqEq).symm
          calc
            (r.1 ∩ s.2).card = (dropFinset p.1 ∩ dropFinset q.2).card := by rw [hpFst, hqSnd]
            _ = (p.1 ∩ q.2).card :=
              inter_card_dropFinset_eq_of_left_last_not_mem hpLeftNot
        exact fun hOne ↦ hOrig (hCardEq.symm.trans hOne)
      have hCardLe : D.card ≤ D1'.card + D2'.card := by
        calc
          D.card ≤ (D1' ∪ D2').card := Finset.card_le_card hCover
          _ ≤ D1'.card + D2'.card := Finset.card_union_le _ _
      have hRec1 : D1.card ≤ 2 ^ n := ih D1 hD1Disjoint hD1Cross
      have hRec2 : D2.card ≤ 2 ^ n := ih D2 hD2Disjoint hD2Cross
      -- The two reduced families live on `Fin n`, so the induction hypothesis finishes.
      calc
        D.card ≤ D1'.card + D2'.card := hCardLe
        _ = D1.card + D2.card := by rw [hD1Card, hD2Card]
        _ ≤ 2 ^ n + 2 ^ n := add_le_add hRec1 hRec2
        _ = 2 * 2 ^ n := by rw [← two_mul]
        _ = 2 ^ (n + 1) := by rw [pow_succ, Nat.mul_comm]

/-- Helper for Theorem 4.54: the disjoint support pairs inside one rectangle matrix supported in
`U^n` form a valid family of size at most `2^n`. -/
private theorem rectangleDisjointPairs_card_le {n : ℕ}
    {M : Matrix (Finset (Fin n)) (Finset (Fin n)) ℕ}
    (hRect : is_rectangle_matrix M)
    (hSupport : matrix_support M ⊆ matrix_support (U^n)) :
    (((Finset.univ.product Finset.univ).filter
        (fun p ↦ Disjoint p.1 p.2 ∧ p ∈ matrix_support M)).card) ≤ 2 ^ n := by
  classical
  rcases (is_rectangle_matrix_iff.mp hRect).2 with ⟨I, J, hI, hJ, hRectSupport⟩
  let A : Finset (Finset (Fin n)) := Finset.univ.filter (fun a ↦ a ∈ I)
  let B : Finset (Finset (Fin n)) := Finset.univ.filter (fun b ↦ b ∈ J)
  have hPairs :
      ((Finset.univ.product Finset.univ).filter
          (fun p ↦ Disjoint p.1 p.2 ∧ p ∈ matrix_support M)) =
        disjointPairs A B := by
    -- Rewrite the rectangle support as a product of finite row and column families.
    ext p
    rcases p with ⟨a, b⟩
    simp [A, B, disjointPairs, hRectSupport, and_assoc]
    constructor
    · rintro ⟨hDisjoint, hI, hJ⟩
      exact ⟨hI, hJ, hDisjoint⟩
    · rintro ⟨hI, hJ, hDisjoint⟩
      exact ⟨hDisjoint, hI, hJ⟩
  rw [hPairs]
  refine validDisjointPairFamily_card_le n (disjointPairs A B) ?_ ?_
  · intro p hp
    exact (mem_disjointPairs_iff.mp hp).2.2
  · intro a ha b hb
    rcases Finset.mem_image.mp ha with ⟨p, hp, hpEq⟩
    rcases Finset.mem_image.mp hb with ⟨q, hq, hqEq⟩
    rcases p with ⟨a', b'⟩
    rcases q with ⟨a'', b''⟩
    have haMem : a' ∈ A := (mem_disjointPairs_iff.mp hp).1
    have hbMem : b'' ∈ B := (mem_disjointPairs_iff.mp hq).2.1
    have hIMem : a' ∈ I := by simpa [A] using haMem
    have hJMem : b'' ∈ J := by simpa [B] using hbMem
    have haEq : a' = a := by simpa using hpEq
    have hbEq : b'' = b := by simpa using hqEq
    have hMemM : (a', b'') ∈ matrix_support M := by
      simpa [hRectSupport] using And.intro hIMem hJMem
    -- The support inclusion turns the cross-condition into the unique-disjointness predicate.
    have hMemU : (a', b'') ∈ matrix_support (U^n) := hSupport hMemM
    simpa [haEq, hbEq] using (uniqueDisjointnessMatrix_memSupport_iff.mp hMemU)

/-- Helper for Theorem 4.54: every disjoint pair in `U^n` can be assigned to one covering
rectangle, yielding a sum bound over the rectangle-local disjoint families. -/
private theorem coverDisjointPairs_card_le_sum {n : ℕ} {k : ℕ}
    {R : Fin k → Matrix (Finset (Fin n)) (Finset (Fin n)) ℕ}
    (hR : is_rectangle_cover (U^n) R) :
    (allDisjointPairs n).card ≤
      ∑ t, (((Finset.univ.product Finset.univ).filter
        (fun p ↦ Disjoint p.1 p.2 ∧ p ∈ matrix_support (R t))).card) := by
  classical
  let localPairs : Fin k → Finset (Finset (Fin n) × Finset (Fin n)) := fun t ↦
    ((Finset.univ.product Finset.univ).filter
      (fun p ↦ Disjoint p.1 p.2 ∧ p ∈ matrix_support (R t)))
  let source : Finset {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n} :=
    (allDisjointPairs n).attach
  have hCovered :
      ∀ p : {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n},
        ∃ t : Fin k, p.1 ∈ localPairs t := by
    intro p
    rcases p with ⟨⟨a, b⟩, hp⟩
    have hp' : a ∈ Finset.univ ∧ b ∈ Finset.univ ∧ Disjoint a b := by
      simpa [allDisjointPairs] using
        ((mem_disjointPairs_iff (A := Finset.univ) (B := Finset.univ) (a := a) (b := b)).1 hp)
    have hMemU : (a, b) ∈ matrix_support (U^n) :=
      disjoint_memSupport_uniqueDisjointnessMatrix hp'.2.2
    rw [hR.support_eq] at hMemU
    rcases Set.mem_iUnion.mp hMemU with ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simpa [localPairs, ht, hp'.2.2]
  let chooseRect :
      {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n} → Fin k :=
    fun p ↦ Classical.choose (hCovered p)
  have hChooseRect :
      ∀ p : {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n},
        p.1 ∈ localPairs (chooseRect p) := by
    intro p
    exact Classical.choose_spec (hCovered p)
  let embed :
      {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n} →
        Σ t, {p // p ∈ localPairs t} := fun p ↦
        ⟨chooseRect p, ⟨p.1, hChooseRect p⟩⟩
  let target : Finset (Σ t, {p // p ∈ localPairs t}) :=
    (Finset.univ : Finset (Fin k)).sigma (fun t ↦ (localPairs t).attach)
  have hMaps :
      Set.MapsTo embed
        ((↑source :
          Set {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n}))
        (↑target : Set (Σ t, {p // p ∈ localPairs t})) := by
    intro p hp
    refine Finset.mem_sigma.mpr ?_
    refine ⟨by simp, ?_⟩
    simpa [embed] using
      (Finset.mem_attach (localPairs (chooseRect p)) ⟨p.1, hChooseRect p⟩)
  have hInj :
      Set.InjOn embed
        ((↑source :
          Set {p : Finset (Fin n) × Finset (Fin n) // p ∈ allDisjointPairs n})) := by
    intro p hp q hq hEq
    apply Subtype.ext
    simpa [embed] using congrArg (fun x ↦ x.2.1) hEq
  have hCard : source.card ≤ target.card :=
    Finset.card_le_card_of_injOn embed hMaps hInj
  -- The sigma target counts exactly the sum of the rectangle-local disjoint families.
  simpa [source, target, localPairs, Finset.card_attach] using hCard

/-- Theorem 4.54. The rectangle covering number of `U^n` is at least `(3 / 2)^n`. -/
theorem unique_disjointness_matrix_rectangle_covering_number_lower_bound
    (n : ℕ) :
    ((3 : ℚ) / 2) ^ n ≤
      rectangle_covering_number (U^n) := by
  classical
  obtain ⟨R, hR⟩ := rectangle_covering_number_spec (U^n)
  let localPairs :
      Fin (rectangle_covering_number (U^n)) →
        Finset (Finset (Fin n) × Finset (Fin n)) := fun t ↦
    ((Finset.univ.product Finset.univ).filter
      (fun p ↦ Disjoint p.1 p.2 ∧ p ∈ matrix_support (R t)))
  have hCount :
      (allDisjointPairs n).card ≤ ∑ t, (localPairs t).card := by
    simpa [localPairs] using coverDisjointPairs_card_le_sum hR
  have hLocal : ∀ t, (localPairs t).card ≤ 2 ^ n := by
    intro t
    refine rectangleDisjointPairs_card_le (hR.rectangles t) ?_
    intro p hp
    rw [hR.support_eq]
    exact Set.mem_iUnion.mpr ⟨t, hp⟩
  have hSum :
      ∑ t, (localPairs t).card ≤ rectangle_covering_number (U^n) * 2 ^ n := by
    calc
      ∑ t, (localPairs t).card ≤ ∑ t, 2 ^ n := by
        simpa using Finset.sum_le_sum (fun t _ ↦ hLocal t)
      _ = rectangle_covering_number (U^n) * 2 ^ n := by simp
  have hNat : 3 ^ n ≤ rectangle_covering_number (U^n) * 2 ^ n := by
    calc
      3 ^ n = (allDisjointPairs n).card := (allDisjointPairs_card n).symm
      _ ≤ ∑ t, (localPairs t).card := hCount
      _ ≤ rectangle_covering_number (U^n) * 2 ^ n := hSum
  have hQ : (3 : ℚ) ^ n ≤ (rectangle_covering_number (U^n) : ℚ) * (2 : ℚ) ^ n := by
    exact_mod_cast hNat
  have hPos : 0 < (2 : ℚ) ^ n := by positivity
  -- Finish by dividing the nat inequality through by the positive factor `(2 : ℚ)^n`.
  rw [div_pow]
  exact (div_le_iff₀ hPos).2 hQ
