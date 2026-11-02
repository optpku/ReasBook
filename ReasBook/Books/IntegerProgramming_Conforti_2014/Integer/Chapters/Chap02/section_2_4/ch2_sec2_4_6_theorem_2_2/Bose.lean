module

public import Mathlib.Tactic
public import Mathlib.Data.ZMod.Basic
public import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_definition_2_26.SteinerTripleSystem
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_4.ch2_sec2_4_6_theorem_2_2.Transport

public section

namespace SteinerTripleSystem

/-- Helper for Theorem 2.2: the Bose construction lives on the cyclic presentation
`ZMod (2 * k + 1) × Fin 3`. -/
abbrev BosePoint (k : ℕ) := ZMod (2 * k + 1) × Fin 3

/-- Helper for Theorem 2.2: the odd cyclic coordinate has a canonical midpoint because doubling is
bijective modulo `2 * k + 1`. -/
def boseMidpoint (k : ℕ) (a b : ZMod (2 * k + 1)) : ZMod (2 * k + 1) :=
  let u : (ZMod (2 * k + 1))ˣ := ZMod.unitOfCoprime 2 (by simp)
  ((u⁻¹ : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1)) * (a + b)

/-- Helper for Theorem 2.2: doubling the Bose midpoint recovers the original pair sum. -/
lemma boseMidpoint_add_self (k : ℕ) (a b : ZMod (2 * k + 1)) :
    boseMidpoint k a b + boseMidpoint k a b = a + b := by
  -- Factor out the doubled inverse of `2`, then cancel it against the unit representing `2`.
  let u : (ZMod (2 * k + 1))ˣ := ZMod.unitOfCoprime 2 (by simp)
  have hu :
      (2 : ZMod (2 * k + 1)) *
          (((u⁻¹ : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1))) = 1 := by
    change
      (((u : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1)) *
        (((u⁻¹ : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1))) = 1)
    simp [u, ZMod.coe_unitOfCoprime]
  calc
    boseMidpoint k a b + boseMidpoint k a b
        = (2 : ZMod (2 * k + 1)) * (boseMidpoint k a b) := by
          simp [two_mul]
    _ = (2 : ZMod (2 * k + 1)) *
          ((((u⁻¹ : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1)) * (a + b))) := by
          simp [boseMidpoint, u]
    _ = ((2 : ZMod (2 * k + 1)) *
          (((u⁻¹ : (ZMod (2 * k + 1))ˣ) : ZMod (2 * k + 1)))) * (a + b) := by
          rw [mul_assoc]
    _ = (1 : ZMod (2 * k + 1)) * (a + b) := by rw [hu]
    _ = a + b := by
          simp

/-- Helper for Theorem 2.2: every pair sum in the odd cyclic coordinate has a unique midpoint. -/
lemma boseMidpoint_existsUnique (k : ℕ) (a b : ZMod (2 * k + 1)) :
    ∃! m : ZMod (2 * k + 1), m + m = a + b := by
  refine ⟨boseMidpoint k a b, boseMidpoint_add_self k a b, ?_⟩
  intro m hm
  have hodd : Odd (2 * k + 1) := by
    exact odd_two_mul_add_one k
  -- Compare two midpoint candidates by subtracting them and using injectivity of doubling.
  have hzero : (m - boseMidpoint k a b) + (m - boseMidpoint k a b) = 0 := by
    calc
      (m - boseMidpoint k a b) + (m - boseMidpoint k a b)
          = (m + m) - (boseMidpoint k a b + boseMidpoint k a b) := by
            abel
      _ = 0 := by
            rw [hm, boseMidpoint_add_self]
            abel
  have hsub : m - boseMidpoint k a b = 0 :=
    (ZMod.add_self_eq_zero_iff_eq_zero hodd).mp hzero
  exact sub_eq_zero.mp hsub

/-- Helper for Theorem 2.2: the vertical Bose triples keep one cyclic coordinate and use all three
colors. -/
def boseVerticalBlock (k : ℕ) (x : ZMod (2 * k + 1)) : Finset (BosePoint k) :=
  { (x, 0), (x, 1), (x, 2) }

/-- Helper for Theorem 2.2: the slanted Bose triples use two same-color points and the midpoint in
the next color. -/
def boseSlantedBlock (k : ℕ) (x y : ZMod (2 * k + 1)) (i : Fin 3) : Finset (BosePoint k) :=
  { (x, i), (y, i), (boseMidpoint k x y, i + 1) }

/-- Helper for Theorem 2.2: the Bose block family consists of the vertical triples and the
same-color midpoint triples. -/
def boseBlocks (k : ℕ) : Set (Finset (BosePoint k)) :=
  {s | (∃ x, s = boseVerticalBlock k x) ∨
      ∃ x y i, x ≠ y ∧ s = boseSlantedBlock k x y i}

/-- Helper for Theorem 2.2: the next Bose color is always different from the current one. -/
lemma boseColor_ne_succ (i : Fin 3) : i ≠ i + 1 := by
  fin_cases i <;> decide

/-- Helper for Theorem 2.2: a vertical Bose block has cardinality `3`. -/
lemma boseVerticalBlock_card (k : ℕ) (x : ZMod (2 * k + 1)) :
    (boseVerticalBlock k x).card = 3 := by
  -- The three color coordinates are visibly distinct.
  simp [boseVerticalBlock]

/-- Helper for Theorem 2.2: a slanted Bose block has cardinality `3` once the two same-color
points are distinct. -/
lemma boseSlantedBlock_card (k : ℕ) {x y : ZMod (2 * k + 1)} (hxy : x ≠ y) (i : Fin 3) :
    (boseSlantedBlock k x y i).card = 3 := by
  -- The first two points differ in the cyclic coordinate, and the third point differs by color.
  refine Finset.card_eq_three.mpr ?_
  refine ⟨(x, i), (y, i), (boseMidpoint k x y, i + 1), ?_, ?_, ?_, ?_⟩
  · intro h
    exact hxy (congrArg Prod.fst h)
  · intro h
    exact boseColor_ne_succ i (congrArg Prod.snd h)
  · intro h
    exact boseColor_ne_succ i (congrArg Prod.snd h)
  · simp [boseSlantedBlock]

/-- Helper for Theorem 2.2: every Bose block lies in the universal ground set. -/
lemma boseBlocks_subset_ground (k : ℕ) :
    ∀ s ∈ boseBlocks k, s ⊆ (Finset.univ : Finset (BosePoint k)) := by
  -- The Bose ground set is `Finset.univ`, so containment is immediate once the family is fixed.
  intro s hs a ha
  simp

/-- Helper for Theorem 2.2: every Bose block has cardinality `3`. -/
lemma boseBlocks_sized (k : ℕ) : (boseBlocks k).Sized 3 := by
  -- Each block is either vertical or slanted, so the dedicated cardinality lemmas close both
  -- branches without unfolding the final existence theorem.
  intro s hs
  rcases hs with (⟨x, rfl⟩ | ⟨x, y, i, hxy, rfl⟩)
  · exact boseVerticalBlock_card k x
  · exact boseSlantedBlock_card k hxy i

/-- Helper for Theorem 2.2: any solution of the midpoint equation is the Bose midpoint. -/
lemma eq_boseMidpoint_of_add_self_eq (k : ℕ) {a b m : ZMod (2 * k + 1)}
    (hm : m + m = a + b) :
    m = boseMidpoint k a b := by
  -- The midpoint theorem packages uniqueness, so matching the doubled sum identifies the point.
  have huniq := boseMidpoint_existsUnique k a b
  exact huniq.unique hm (boseMidpoint_add_self k a b)

/-- Helper for Theorem 2.2: once the midpoint and one endpoint are known, the other endpoint is
determined by subtraction. -/
lemma boseRight_eq_of_midpoint_eq (k : ℕ) {x y m : ZMod (2 * k + 1)}
    (hm : boseMidpoint k x y = m) :
    y = m + m - x := by
  -- Rewrite the doubled-midpoint equation and solve for the right endpoint additively.
  have hsum : m + m = x + y := by
    simpa [hm] using boseMidpoint_add_self k x y
  calc
    y = (x + y) - x := by abel
    _ = (m + m) - x := by rw [← hsum]

/-- Helper for Theorem 2.2: the left endpoint is equally determined by the midpoint equation. -/
lemma boseLeft_eq_of_midpoint_eq (k : ℕ) {x y m : ZMod (2 * k + 1)}
    (hm : boseMidpoint k x y = m) :
    x = m + m - y := by
  -- This is the symmetric endpoint reconstruction obtained from the same doubled-midpoint
  -- identity.
  have hsum : m + m = x + y := by
    simpa [hm] using boseMidpoint_add_self k x y
  calc
    x = (x + y) - y := by abel
    _ = (m + m) - y := by rw [← hsum]

/-- Helper for Theorem 2.2: swapping the two same-color endpoints does not change a slanted Bose
block. -/
lemma boseSlantedBlock_swap (k : ℕ) (x y : ZMod (2 * k + 1)) (i : Fin 3) :
    boseSlantedBlock k x y i = boseSlantedBlock k y x i := by
  -- The block is defined by an unordered same-color pair together with their midpoint.
  ext z
  simp [boseSlantedBlock, boseMidpoint, add_comm, or_left_comm]

/-- Helper for Theorem 2.2: two distinct colors in `Fin 3` differ by one cyclic step in one of
the two orientations. -/
lemma fin3_eq_add_one_or_eq_add_one (i j : Fin 3) (hij : i ≠ j) :
    j = i + 1 ∨ i = j + 1 := by
  -- On `Fin 3`, checking the three colors directly isolates the only two cyclic orientations.
  fin_cases i <;> fin_cases j <;> simp at hij ⊢

/-- Helper for Theorem 2.2: a mixed-color pair with one shared cyclic coordinate is covered by the
vertical Bose block through that coordinate. -/
lemma boseCoverOfMixedColorsSameCoordOriented (k : ℕ) (a : ZMod (2 * k + 1)) (i : Fin 3) :
    ∃! s, s ∈ boseBlocks k ∧ ({(a, i), (a, i + 1)} : Finset (BosePoint k)) ⊆ s := by
  refine ⟨boseVerticalBlock k a, ?_, ?_⟩
  · constructor
    · -- The shared-coordinate witness is the vertical block through that cyclic point.
      exact Or.inl ⟨a, rfl⟩
    · intro x hx
      have hx' : x = (a, i) ∨ x = (a, i + 1) := by
        fin_cases i <;> simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm,
          or_assoc] using hx
      rcases hx' with rfl | rfl <;> fin_cases i <;> simp [boseVerticalBlock]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair : (a, i) ∈ ({(a, i), (a, i + 1)} : Finset (BosePoint k)) := by
      simp [boseColor_ne_succ i]
    have hvPair : (a, i + 1) ∈ ({(a, i), (a, i + 1)} : Finset (BosePoint k)) := by
      simp
    rcases hsB with (⟨x, rfl⟩ | ⟨x, y, i₀, hxy, rfl⟩)
    · -- A vertical candidate is determined by either of the two contained points.
      have huVert : (a, i) ∈ boseVerticalBlock k x := hsub huPair
      have hxa : a = x := by
        fin_cases i <;> simpa [boseVerticalBlock] using huVert
      subst x
      rfl
    · -- Route correction: this branch rules out slanted candidates by showing the midpoint
      -- equality would force the two same-color endpoints to coincide.
      have huSlant : (a, i) ∈ boseSlantedBlock k x y i₀ := hsub huPair
      have hvSlant : (a, i + 1) ∈ boseSlantedBlock k x y i₀ := hsub hvPair
      have hi₀ : i₀ = i := by
        -- The two colors `i` and `i + 1` fix the slanted-block orientation uniquely.
        fin_cases i <;> fin_cases i₀ <;>
          simp [boseSlantedBlock] at huSlant hvSlant ⊢
      subst hi₀
      have huEnds : a = x ∨ a = y := by
        -- The point of color `i` must be one of the two same-color endpoints.
        simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using huSlant
      have hmid : boseMidpoint k x y = a := by
        -- The point of color `i + 1` is forced to be the midpoint-colored vertex.
        exact (by simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using hvSlant : a = _).symm
      rcases huEnds with hax | hay
      · -- Recovering the other endpoint from the midpoint equation contradicts distinctness.
        have hy' : y = a := by
          simpa [hax] using boseRight_eq_of_midpoint_eq k hmid
        exact (hxy (by calc
          x = a := hax.symm
          _ = y := hy'.symm)).elim
      · -- The symmetric endpoint recovery gives the same contradiction.
        have hx' : x = a := by
          simpa [hay] using boseLeft_eq_of_midpoint_eq k hmid
        exact (hxy (by calc
          x = a := hx'
          _ = y := hay)).elim

/-- Helper for Theorem 2.2: a mixed-color pair with distinct cyclic coordinates is covered by the
unique slanted Bose block determined by endpoint recovery from the midpoint coordinate. -/
lemma boseCoverOfMixedColorsDistinctCoordsOriented (k : ℕ)
    {a b : ZMod (2 * k + 1)} (hab : a ≠ b) (i : Fin 3) :
    ∃! s, s ∈ boseBlocks k ∧ ({(a, i), (b, i + 1)} : Finset (BosePoint k)) ⊆ s := by
  let c : ZMod (2 * k + 1) := b + b - a
  have hmid : boseMidpoint k a c = b := by
    -- The recovered endpoint `c` is defined so that `b` solves the midpoint equation for `a`
    -- and `c`.
    have hb : b + b = a + c := by
      dsimp [c]
      abel
    exact (eq_boseMidpoint_of_add_self_eq k hb).symm
  have hca : c ≠ a := by
    -- If the recovered endpoint collapsed back to `a`, the midpoint uniqueness would identify
    -- `a` and `b`, contradicting the distinct-coordinate hypothesis.
    intro hca
    have haa : a = boseMidpoint k a a :=
      eq_boseMidpoint_of_add_self_eq k (by abel)
    have hba : b = a := by
      calc
        b = boseMidpoint k a c := hmid.symm
        _ = boseMidpoint k a a := by simp [hca]
        _ = a := haa.symm
    exact hab hba.symm
  refine ⟨boseSlantedBlock k a c i, ?_, ?_⟩
  · constructor
    · -- The witness block uses the given endpoint and the uniquely recovered second endpoint.
      exact Or.inr ⟨a, c, i, by
        intro hac
        exact hca hac.symm, rfl⟩
    · intro x hx
      have hx' : x = (a, i) ∨ x = (b, i + 1) := by
        fin_cases i <;> simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_left_comm,
          or_assoc] using hx
      rcases hx' with rfl | rfl
      · simp [boseSlantedBlock]
      · simp [boseSlantedBlock, hmid]
  · intro s hs
    rcases hs with ⟨hsB, hsub⟩
    have huPair : (a, i) ∈ ({(a, i), (b, i + 1)} : Finset (BosePoint k)) := by
      simp [hab, boseColor_ne_succ i]
    have hvPair : (b, i + 1) ∈ ({(a, i), (b, i + 1)} : Finset (BosePoint k)) := by
      simp
    rcases hsB with (⟨x, rfl⟩ | ⟨x, y, i₀, hxy, rfl⟩)
    · -- A vertical block cannot contain two points with different cyclic coordinates.
      have huVert : (a, i) ∈ boseVerticalBlock k x := hsub huPair
      have hvVert : (b, i + 1) ∈ boseVerticalBlock k x := hsub hvPair
      fin_cases i <;> simp [boseVerticalBlock] at huVert hvVert
      all_goals exact (hab (huVert.trans hvVert.symm)).elim
    · -- Route correction: once the color orientation is fixed, the midpoint equation recovers the
      -- missing same-color endpoint uniquely.
      have huSlant : (a, i) ∈ boseSlantedBlock k x y i₀ := hsub huPair
      have hvSlant : (b, i + 1) ∈ boseSlantedBlock k x y i₀ := hsub hvPair
      have hi₀ : i₀ = i := by
        -- The colors `i` and `i + 1` force the slanted block to use color `i`.
        fin_cases i <;> fin_cases i₀ <;>
          simp [boseSlantedBlock] at huSlant hvSlant ⊢
      subst hi₀
      have huEnds : a = x ∨ a = y := by
        -- The point of color `i` is one of the same-color endpoints.
        simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using huSlant
      have hmid' : boseMidpoint k x y = b := by
        -- The point of color `i + 1` is forced to be the midpoint-colored vertex.
        exact (by simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using hvSlant : b = _).symm
      rcases huEnds with hax | hay
      · -- If `a = x`, endpoint recovery identifies the other endpoint with `c`.
        have hy' : y = c := by
          dsimp [c]
          simpa [hax] using boseRight_eq_of_midpoint_eq k hmid'
        subst hax
        subst hy'
        rfl
      · -- If `a = y`, swap the two same-color endpoints after recovering `x = c`.
        have hx' : x = c := by
          dsimp [c]
          simpa [hay] using boseLeft_eq_of_midpoint_eq k hmid'
        subst hay
        subst hx'
        rw [boseSlantedBlock_swap]

/-- Helper for Theorem 2.2: a literal pair of distinct Bose points is covered by a unique Bose
block. -/
lemma boseCoverOfTwoPoints (k : ℕ) {u v : BosePoint k} (huv : u ≠ v) :
    ∃! s, s ∈ boseBlocks k ∧ ({u, v} : Finset (BosePoint k)) ⊆ s := by
  rcases u with ⟨a, i⟩
  rcases v with ⟨b, j⟩
  by_cases hij : i = j
  · subst hij
    have hab : a ≠ b := by
      -- Distinct Bose points of the same color must differ in the cyclic coordinate.
      intro hab
      exact huv (Prod.ext hab rfl)
    refine ⟨boseSlantedBlock k a b i, ?_, ?_⟩
    · constructor
      · -- The witness is exactly the same-color slanted block on the pair.
        exact Or.inr ⟨a, b, i, hab, rfl⟩
      · -- Both endpoints are visibly members of the witness block.
        intro x hx
        have hx' : x = (a, i) ∨ x = (b, i) := by
          simpa [hab] using hx
        rcases hx' with rfl | rfl <;> simp [boseSlantedBlock, hab]
    · intro s hs
      rcases hs with ⟨hsB, hsub⟩
      have huPair : (a, i) ∈ ({(a, i), (b, i)} : Finset (BosePoint k)) := by
        simp [hab]
      have hvPair : (b, i) ∈ ({(a, i), (b, i)} : Finset (BosePoint k)) := by
        simp
      rcases hsB with (⟨x, rfl⟩ | ⟨x, y, i₀, hxy, rfl⟩)
      · -- A vertical block cannot contain two distinct points of the same color.
        have huVert : (a, i) ∈ boseVerticalBlock k x := hsub huPair
        have hvVert : (b, i) ∈ boseVerticalBlock k x := hsub hvPair
        fin_cases i <;> simp [boseVerticalBlock] at huVert hvVert
        all_goals exact (hab (huVert.trans hvVert.symm)).elim
      · -- Any slanted block covering the pair must use the same color and the same unordered
        -- same-color endpoints.
        have huSlant : (a, i) ∈ boseSlantedBlock k x y i₀ := hsub huPair
        have hvSlant : (b, i) ∈ boseSlantedBlock k x y i₀ := hsub hvPair
        by_cases hi₀ : i₀ = i
        · subst hi₀
          have haCases : a = x ∨ a = y := by
            simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using huSlant
          have hbCases : b = x ∨ b = y := by
            simpa [boseSlantedBlock, hxy, boseColor_ne_succ] using hvSlant
          rcases haCases with rfl | rfl
          · rcases hbCases with hbx | hby
            · exact (hab hbx.symm).elim
            · subst hby
              rfl
          · rcases hbCases with hbx | hby
            · subst hbx
              rw [boseSlantedBlock_swap]
            · exact (hab hby.symm).elim
        · -- If the slanted block used a different color, both same-color points would have to be
          -- the unique midpoint-colored vertex, which contradicts `a ≠ b`.
          exfalso
          fin_cases i <;> fin_cases i₀ <;>
            simp [boseSlantedBlock] at huSlant hvSlant hi₀
          all_goals exact hab (huSlant.trans hvSlant.symm)
  · by_cases hab : a = b
    · subst hab
      rcases fin3_eq_add_one_or_eq_add_one i j hij with hji | hij'
      · -- Route correction: normalize the mixed-color pair to the forward cyclic orientation and
        -- dispatch to the dedicated same-coordinate classifier.
        simpa [hji] using boseCoverOfMixedColorsSameCoordOriented k a i
      · -- If the colors arrive in the reverse orientation, swap the literal pair first.
        have hpair :
            ({(a, j + 1), (a, j)} : Finset (BosePoint k)) =
              ({(a, j), (a, j + 1)} : Finset (BosePoint k)) := by
          ext x
          constructor <;> intro hx <;>
            simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm] using
              hx
        simpa [hij', hpair] using boseCoverOfMixedColorsSameCoordOriented k a j
    · rcases fin3_eq_add_one_or_eq_add_one i j hij with hji | hij'
      · -- Normalize to the oriented mixed-color distinct-coordinate helper.
        simpa [hji] using
          boseCoverOfMixedColorsDistinctCoordsOriented k hab i
      · -- Swap the pair when the colors come in the reverse cyclic orientation.
        have hpair :
            ({(a, j + 1), (b, j)} : Finset (BosePoint k)) =
              ({(b, j), (a, j + 1)} : Finset (BosePoint k)) := by
          ext x
          constructor <;> intro hx <;>
            simpa [Finset.mem_insert, Finset.mem_singleton, eq_comm, or_comm] using
              hx
        simpa [hij', hpair] using
          (boseCoverOfMixedColorsDistinctCoordsOriented k
            (by
              intro hba
              exact hab hba.symm) j)

/-- Helper for Theorem 2.2: every `2`-subset of the Bose ground type should lie in a unique Bose
block. -/
lemma bosePairCover (k : ℕ) :
    ∀ p, p ∈ (Finset.univ : Finset (BosePoint k)).powersetCard 2 →
      ∃! s, s ∈ boseBlocks k ∧ p ⊆ s := by
  intro p hp
  -- Route correction: the `powersetCard` bookkeeping is now isolated, so the combinatorial proof
  -- runs entirely on a literal distinct pair.
  obtain ⟨u, v, huv, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp hp).2
  exact boseCoverOfTwoPoints k huv

/-- Helper for Theorem 2.2: the Bose family should supply a Steiner triple system for each order
`6k + 3`, realized on `ZMod (2 * k + 1) × Fin 3`. -/
theorem boseExistsOn (k : ℕ) :
    ∃ S : Set (Finset (ZMod (2 * k + 1) × Fin 3)), IsOn Finset.univ S := by
  refine ⟨boseBlocks k, IsOn.ofSubsetGroundSizedAndPairCover ?_ ?_ ?_⟩
  · -- Ground containment is already packaged by the local Bose block-family lemma.
    exact boseBlocks_subset_ground k
  · -- Uniformity is reduced to the vertical/slanted block cardinality lemmas.
    exact boseBlocks_sized k
  · -- Final assembly now depends only on the isolated pair-cover interface.
    exact bosePairCover k

end SteinerTripleSystem
