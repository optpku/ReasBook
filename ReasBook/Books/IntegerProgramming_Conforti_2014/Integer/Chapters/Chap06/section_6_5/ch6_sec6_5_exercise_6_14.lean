import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap06.section_6_2_2.ch6_sec6_2_2_theorem_6_18
import Mathlib.Analysis.LocallyConvex.Separation

-- Declarations for this item will be appended below by the statement pipeline.

-- Domain-style sampling for this refine pass:
-- * primary domain: `S`-free / maximal `S`-free convex sets in `ℝ^q`
-- * core/canonical owners inspected: `is_free_of`, `is_maximal_free_of`,
--   `is_lattice_free`, `is_maximal_lattice_free`
-- * chapter lattice owner reused here: `ℤ^q` together with `mem_integerVectors_iff`
-- * source-facing owner kept here: `nonnegativeIntegerVectors` with notation `ℤ_+^q`
-- * primitive vs derived split: `nonnegativeIntegerVectors` is primitive data; the free/maximal
--   predicates remain thin specializations of the Chapter 6 generic owners; the halfspace owner is
--   stated intrinsically via the linear functional `dotProduct a`

section Exercise614

variable {q : ℕ}

local notation "R2" => Fin 2 → ℝ

open scoped IntegerVectorNotation

/-- The embedded nonnegative integer lattice `ℤ_+^q = ℤ^q ∩ ℝ_+^q ⊆ ℝ^q`. -/
def nonnegativeIntegerVectors (q : ℕ) : Set (Fin q → ℝ) :=
  ℤ^q ∩ Set.Ici (0 : Fin q → ℝ)

namespace NonnegativeIntegerVectorNotation

scoped notation "ℤ_+^" n:max => nonnegativeIntegerVectors n

end NonnegativeIntegerVectorNotation

open scoped NonnegativeIntegerVectorNotation

/-- Membership in `ℤ_+^q` is exactly membership in `ℤ^q` together with coordinatewise
nonnegativity. -/
theorem mem_nonnegativeIntegerVectors_iff
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      r ∈ ℤ^q ∧ 0 ≤ r :=
  Iff.rfl

/-- A real vector lies in `ℤ_+^q` exactly when each coordinate is a nonnegative integer. -/
theorem mem_nonnegativeIntegerVectors_iff_forall
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      ∀ i, r i ∈ Set.range (Int.cast : ℤ → ℝ) ∧ 0 ≤ r i := by
  constructor
  · intro hr
    rcases mem_nonnegativeIntegerVectors_iff.mp hr with ⟨hr_int, hr_nonneg⟩
    intro i
    exact ⟨(mem_integerVectors_iff_forall.mp hr_int) i, hr_nonneg i⟩
  · intro h
    exact (mem_nonnegativeIntegerVectors_iff).2
      ⟨(mem_integerVectors_iff_forall).2 (fun i ↦ (h i).1), fun i ↦ (h i).2⟩

/-- Membership in `ℤ_+^q` means being the real-valued coercion of a nonnegative integer vector. -/
theorem mem_nonnegativeIntegerVectors_iff_exists
    {r : Fin q → ℝ} :
    r ∈ ℤ_+^q ↔
      ∃ z : Fin q → ℕ, r = Nat.cast ∘ z := by
  constructor
  · rintro ⟨hr_int, hr_nonneg⟩
    rcases (mem_integerVectors_iff.mp hr_int) with ⟨z, rfl⟩
    refine ⟨fun i ↦ Int.toNat (z i), ?_⟩
    funext i
    have hzi_nonneg : 0 ≤ z i := by
      have hri : (0 : ℝ) ≤ (z i : ℝ) := by
        simpa using hr_nonneg i
      exact (Int.cast_nonneg_iff).1 hri
    change (z i : ℝ) = (Int.toNat (z i) : ℝ)
    exact_mod_cast (Int.toNat_of_nonneg hzi_nonneg).symm
  · rintro ⟨z, rfl⟩
    refine ⟨?_, ?_⟩
    · refine (mem_integerVectors_iff).2 ⟨fun i ↦ (z i : ℤ), ?_⟩
      funext i
      simp
    · exact fun i ↦ Nat.cast_nonneg (z i)

/-- Every embedded nonnegative integer vector is, in particular, an embedded integer vector. -/
theorem nonnegativeIntegerVectors_subset_integerVectors :
    ℤ_+^q ⊆ (ℤ^q : Set (Fin q → ℝ)) := by
  intro r hr
  exact (mem_nonnegativeIntegerVectors_iff.mp hr).1

/-- A convex set in `ℝ^q` is `ℤ_+^q`-free when its interior contains no embedded nonnegative
integer point. -/
def is_nonnegative_integer_free (K : Set (Fin q → ℝ)) : Prop :=
  is_free_of (ℤ_+^q) K

/-- `is_nonnegative_integer_free K` unfolds to the assertion that no point of `ℤ_+^q` lies in the
interior of `K`. -/
theorem is_nonnegative_integer_free_iff
    {K : Set (Fin q → ℝ)} :
    is_nonnegative_integer_free K ↔
      ∀ z : Fin q → ℕ, (Nat.cast ∘ z) ∉ interior K := by
  rw [is_nonnegative_integer_free, is_free_of_iff]
  constructor
  · intro h z
    exact h _ ((mem_nonnegativeIntegerVectors_iff_exists).2 ⟨z, rfl⟩)
  · intro h x hx
    rcases (mem_nonnegativeIntegerVectors_iff_exists).1 hx with ⟨z, rfl⟩
    exact h z

/-- If `K` is `ℤ_+^q`-free, then every embedded nonnegative integer point lies outside the
interior of `K`. -/
theorem is_nonnegative_integer_free.not_mem_interior
    {K : Set (Fin q → ℝ)}
    (hK : is_nonnegative_integer_free K)
    {x : Fin q → ℝ}
    (hx : x ∈ ℤ_+^q) :
    x ∉ interior K :=
  is_free_of.not_mem_interior hK hx

/-- A convex set in `ℝ^q` is maximal `ℤ_+^q`-free when it is `ℤ_+^q`-free and admits no strictly
larger convex `ℤ_+^q`-free superset. -/
def is_maximal_nonnegative_integer_free (K : Set (Fin q → ℝ)) : Prop :=
  is_maximal_free_of (ℤ_+^q) K

/-- `is_maximal_nonnegative_integer_free K` unfolds to convexity, `ℤ_+^q`-freeness, and
maximality among convex `ℤ_+^q`-free supersets. -/
theorem is_maximal_nonnegative_integer_free_iff
    {K : Set (Fin q → ℝ)} :
    is_maximal_nonnegative_integer_free K ↔
      Convex ℝ K ∧
        is_nonnegative_integer_free K ∧
          ∀ L : Set (Fin q → ℝ),
            K ⊆ L → Convex ℝ L → is_nonnegative_integer_free L → L = K :=
  Iff.rfl

/-- A maximal `ℤ_+^q`-free set is convex. -/
theorem is_maximal_nonnegative_integer_free.convex
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K) :
    Convex ℝ K :=
  is_maximal_free_of.convex hK

/-- A maximal `ℤ_+^q`-free set is `ℤ_+^q`-free. -/
theorem is_maximal_nonnegative_integer_free.free
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K) :
    is_nonnegative_integer_free K :=
  is_maximal_free_of.free hK

/-- Maximality among convex `ℤ_+^q`-free supersets gives equality with any larger convex
`ℤ_+^q`-free superset. -/
theorem is_maximal_nonnegative_integer_free.eq_of_subset
    {K : Set (Fin q → ℝ)}
    (hK : is_maximal_nonnegative_integer_free K)
    {L : Set (Fin q → ℝ)}
    (hKL : K ⊆ L)
    (hL_convex : Convex ℝ L)
    (hL_free : is_nonnegative_integer_free L) :
    L = K :=
  is_maximal_free_of.eq_of_subset hK hKL hL_convex hL_free

/-- The halfspace through the origin with outward normal `a` in `ℝ²`. -/
def nonnegative_supporting_halfspace (a : R2) : Set R2 :=
  {x : R2 | dotProduct a x ≤ 0}

/-- Helper for Exercise 6.14: a strict supporting inequality gives an interior point of the
supporting halfspace. -/
lemma mem_interior_nonnegativeSupportingHalfspace_of_lt
    {a x : R2}
    (hx : dotProduct a x < 0) :
    x ∈ interior (nonnegative_supporting_halfspace a) := by
  -- A strict inequality belongs to the interior of the corresponding closed halfspace.
  have hcont : Continuous fun y : R2 ↦ dotProduct a y := by
    continuity
  exact
    (lt_subset_interior_le hcont continuous_const)
      (by simpa [nonnegative_supporting_halfspace] using hx)

/-- Helper for Exercise 6.14: the interior of a nontrivial supporting halfspace is cut out by the
strict inequality. -/
lemma interior_nonnegativeSupportingHalfspace_eq
    {a : R2}
    (ha : a ≠ 0) :
    interior (nonnegative_supporting_halfspace a) = {x : R2 | dotProduct a x < 0} := by
  ext x
  constructor
  · intro hx
    -- Interior points cannot lie on the boundary hyperplane of a nontrivial halfspace.
    have hxmem : x ∈ nonnegative_supporting_halfspace a := interior_subset hx
    by_contra hnotlt
    have hxeq : dotProduct a x = 0 := by
      have hxge : 0 ≤ dotProduct a x := le_of_not_gt hnotlt
      exact le_antisymm hxmem hxge
    rw [mem_interior_iff_mem_nhds] at hx
    rcases Metric.mem_nhds_iff.mp hx with ⟨ε, hεpos, hεsubset⟩
    have hnorm_pos : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have hself_nonneg : 0 ≤ dotProduct a a := by
      unfold dotProduct
      exact Finset.sum_nonneg (fun i _ ↦ mul_self_nonneg (a i))
    have hself_ne : dotProduct a a ≠ 0 := by
      intro hzero
      exact ha ((dotProduct_self_eq_zero).1 hzero)
    have hself_pos : 0 < dotProduct a a :=
      lt_of_le_of_ne hself_nonneg (Ne.symm hself_ne)
    let t : ℝ := ε / (2 * ‖a‖)
    have ht_pos : 0 < t := by
      dsimp [t]
      exact div_pos hεpos (by positivity)
    have ht_eq : t * ‖a‖ = ε / 2 := by
      dsimp [t]
      field_simp [hnorm_pos.ne']
    have ht_norm : ‖t • a‖ < ε := by
      calc
        ‖t • a‖ = |t| * ‖a‖ := norm_smul _ _
        _ = t * ‖a‖ := by rw [abs_of_nonneg ht_pos.le]
        _ = ε / 2 := ht_eq
        _ < ε := by linarith
    have hyball : x + t • a ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using ht_norm
    have hymem : x + t • a ∈ nonnegative_supporting_halfspace a := hεsubset hyball
    have hypos : 0 < dotProduct a (x + t • a) := by
      have hycalc : dotProduct a (x + t • a) = t * dotProduct a a := by
        rw [dotProduct_add, dotProduct_smul, hxeq, zero_add, smul_eq_mul]
      rw [hycalc]
      exact mul_pos ht_pos hself_pos
    have hynotmem : x + t • a ∉ nonnegative_supporting_halfspace a := by
      intro hymem'
      exact (not_le_of_gt hypos) hymem'
    exact hynotmem hymem
  · intro hx
    -- The strict sublevel set is open and sits inside the closed halfspace.
    exact mem_interior_nonnegativeSupportingHalfspace_of_lt hx

/-- Helper for Exercise 6.14: `¬ is_lattice_free K` supplies an interior integer witness, hence a
nonempty interior. -/
lemma nonemptyInterior_of_not_lattice_free
    {K : Set R2}
    (hnot : ¬ is_lattice_free K) :
    (interior K).Nonempty := by
  -- Negating lattice-freeness produces an embedded integer point in the interior.
  rw [is_lattice_free_iff] at hnot
  push Not at hnot
  rcases hnot with ⟨z, hz⟩
  exact ⟨Int.cast ∘ z, hz⟩

/-- Helper for Exercise 6.14: a supporting halfspace with a nonzero nonnegative normal is maximal
`ℤ_+^2`-free and still contains a negative integer point in its interior. -/
lemma nonnegativeSupportingHalfspace_maximal_and_notLatticeFree
    {a : R2}
    (ha_nonneg : 0 ≤ a)
    (ha : a ≠ 0) :
    is_maximal_nonnegative_integer_free (nonnegative_supporting_halfspace a) ∧
      ¬ is_lattice_free (nonnegative_supporting_halfspace a) := by
  have hlinear : IsLinearMap ℝ (fun x : R2 ↦ dotProduct a x) :=
    IsLinearMap.mk (dotProduct_add a) (fun c x ↦ dotProduct_smul c a x)
  have hconv : Convex ℝ (nonnegative_supporting_halfspace a) := by
    -- The halfspace is cut out by a linear inequality.
    simpa [nonnegative_supporting_halfspace] using
      convex_halfSpace_le hlinear 0
  have hfree : is_nonnegative_integer_free (nonnegative_supporting_halfspace a) := by
    -- A nonnegative lattice point has nonnegative dot product, so it cannot satisfy the strict
    -- interior inequality.
    rw [is_nonnegative_integer_free_iff]
    intro z hz
    have hz_nonneg : 0 ≤ (Nat.cast ∘ z : R2) := by
      exact ((mem_nonnegativeIntegerVectors_iff.mp
        ((mem_nonnegativeIntegerVectors_iff_exists).2 ⟨z, rfl⟩))).2
    have hdot_nonneg : 0 ≤ dotProduct a (Nat.cast ∘ z : R2) :=
      dotProduct_nonneg_of_nonneg ha_nonneg hz_nonneg
    have hdot_lt : dotProduct a (Nat.cast ∘ z : R2) < 0 := by
      simpa [interior_nonnegativeSupportingHalfspace_eq ha] using hz
    exact (not_lt_of_ge hdot_nonneg) hdot_lt
  have hmax : is_maximal_nonnegative_integer_free (nonnegative_supporting_halfspace a) := by
    refine ⟨hconv, hfree, ?_⟩
    intro L hHL hLconv hLfree
    apply Set.Subset.antisymm
    · intro y hyL
      by_contra hyH
      -- If `y` lies beyond the supporting boundary, then the midpoint of `y` and `-y` forces
      -- the forbidden point `0` into the interior of `L`.
      have hy_pos : 0 < dotProduct a y := by
        simpa [nonnegative_supporting_halfspace, not_le] using hyH
      have hnegy_lt : dotProduct a (-y) < 0 := by
        simpa using (neg_neg_iff_pos.mpr hy_pos)
      have hnegy_int_H : -y ∈ interior (nonnegative_supporting_halfspace a) :=
        mem_interior_nonnegativeSupportingHalfspace_of_lt hnegy_lt
      have hnegy_int_L : -y ∈ interior L := interior_mono hHL hnegy_int_H
      have hzero_int : (0 : R2) ∈ interior L := by
        have hmid :
            (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • (-y) ∈ interior L := by
          exact hLconv.combo_self_interior_mem_interior hyL hnegy_int_L (by norm_num)
            (by norm_num) (by ring)
        simpa using hmid
      have hzero_mem : (0 : R2) ∈ ℤ_+^2 := by
        exact (mem_nonnegativeIntegerVectors_iff_exists).2 ⟨0, by funext i; simp⟩
      exact (is_nonnegative_integer_free.not_mem_interior hLfree hzero_mem) hzero_int
    · exact hHL
  have hnot_lattice_free : ¬ is_lattice_free (nonnegative_supporting_halfspace a) := by
    -- A positive coordinate of `a` exposes a negative unit vector in the interior.
    have hcoord : ∃ i : Fin 2, 0 < a i := by
      by_cases h0 : a 0 = 0
      · have h1 : a 1 ≠ 0 := by
          intro h1
          apply ha
          funext i
          fin_cases i <;> simp [h0, h1]
        exact ⟨1, lt_of_le_of_ne (ha_nonneg 1) (Ne.symm h1)⟩
      · exact ⟨0, lt_of_le_of_ne (ha_nonneg 0) (Ne.symm h0)⟩
    rcases hcoord with ⟨i, hi⟩
    intro hlf
    have hlt : dotProduct a (Int.cast ∘ Pi.single i (-1 : ℤ) : R2) < 0 := by
      fin_cases i
      · simpa [dotProduct] using (neg_neg_iff_pos.mpr hi)
      · simpa [dotProduct] using (neg_neg_iff_pos.mpr hi)
    exact
      (is_lattice_free_iff.mp hlf (Pi.single i (-1 : ℤ)))
        (by simpa [interior_nonnegativeSupportingHalfspace_eq ha] using hlt)
  exact ⟨hmax, hnot_lattice_free⟩

/-- Helper for Exercise 6.14: once a maximal `ℤ_+^2`-free convex set contains an interior integer
point, maximality against its closure forces the set to be closed. -/
lemma maximalNonnegativeIntegerFree_isClosed_of_notLatticeFree
    {K : Set R2}
    (hK : is_maximal_nonnegative_integer_free K)
    (hnot : ¬ is_lattice_free K) :
    IsClosed K := by
  -- Compare `K` with its closure, which stays `ℤ_+^2`-free because the interior does not change.
  have hconv : Convex ℝ K := is_maximal_nonnegative_integer_free.convex hK
  have hinterior : (interior K).Nonempty := nonemptyInterior_of_not_lattice_free hnot
  have hclosureFree : is_nonnegative_integer_free (closure K) := by
    rw [is_nonnegative_integer_free_iff]
    intro z
    rw [hconv.interior_closure_eq_interior_of_nonempty_interior hinterior]
    exact (is_nonnegative_integer_free_iff.mp
      (is_maximal_nonnegative_integer_free.free hK)) z
  have hclosure_eq : closure K = K :=
    is_maximal_nonnegative_integer_free.eq_of_subset hK subset_closure hconv.closure hclosureFree
  exact closure_eq_iff_isClosed.mp hclosure_eq

/-- Helper for Exercise 6.14: if a convex set contains every nonnegative integer point, then it
contains the whole square `[0,2]^2`. -/
lemma twoSquare_subset_of_containsAllNonnegativeIntegers
    {K : Set R2}
    (hconv : Convex ℝ K)
    (hints : ∀ n : Fin 2 → ℕ, (Nat.cast ∘ n : R2) ∈ K) :
    Set.Icc (0 : R2) (fun _ ↦ (2 : ℝ)) ⊆ K := by
  intro x hx
  let sx : ℝ := x 0 / 2
  let sy : ℝ := x 1 / 2
  let bottom : R2 := fun j ↦ if j = 0 then x 0 else 0
  let top : R2 := fun j ↦ if j = 0 then x 0 else 2
  have hsx_nonneg : 0 ≤ sx := by
    dsimp [sx]
    exact div_nonneg (hx.1 0) (by positivity)
  have hsx_le_one : sx ≤ 1 := by
    dsimp [sx]
    have hx0_le : x 0 ≤ 2 := hx.2 0
    linarith
  have hsy_nonneg : 0 ≤ sy := by
    dsimp [sy]
    exact div_nonneg (hx.1 1) (by positivity)
  have hsy_le_one : sy ≤ 1 := by
    dsimp [sy]
    have hx1_le : x 1 ≤ 2 := hx.2 1
    linarith
  have hzero_mem : (0 : R2) ∈ K := by
    simpa using hints 0
  have hright_mem : (Nat.cast ∘ fun j : Fin 2 ↦ if j = 0 then 2 else 0 : R2) ∈ K := by
    simpa using hints (fun j : Fin 2 ↦ if j = 0 then 2 else 0)
  have htop_mem : (Nat.cast ∘ fun j : Fin 2 ↦ if j = 1 then 2 else 0 : R2) ∈ K := by
    simpa using hints (fun j : Fin 2 ↦ if j = 1 then 2 else 0)
  have hcorner_mem : (fun _ : Fin 2 ↦ (2 : ℝ)) ∈ K := by
    simpa using hints (fun _ : Fin 2 ↦ 2)
  have hbottom_mem : bottom ∈ K := by
    -- Interpolate along the bottom edge of the square.
    have hcombo :
        (1 - sx) • (0 : R2) + sx • (Nat.cast ∘ fun j : Fin 2 ↦ if j = 0 then 2 else 0 : R2) ∈ K := by
      exact hconv hzero_mem hright_mem (sub_nonneg.mpr hsx_le_one) hsx_nonneg (by ring)
    have hbottom_eq :
        bottom =
          (1 - sx) • (0 : R2) + sx •
            (Nat.cast ∘ fun j : Fin 2 ↦ if j = 0 then 2 else 0 : R2) := by
      ext j
      fin_cases j <;> simp [bottom, sx] <;> ring
    rw [hbottom_eq]
    exact hcombo
  have htopEdge_mem : top ∈ K := by
    -- Interpolate along the top edge of the square.
    have hcombo :
        (1 - sx) • (Nat.cast ∘ fun j : Fin 2 ↦ if j = 1 then 2 else 0 : R2) + sx •
          (fun _ : Fin 2 ↦ (2 : ℝ)) ∈ K := by
      exact hconv htop_mem hcorner_mem (sub_nonneg.mpr hsx_le_one) hsx_nonneg (by ring)
    have htop_eq :
        top =
          (1 - sx) • (Nat.cast ∘ fun j : Fin 2 ↦ if j = 1 then 2 else 0 : R2) + sx •
            (fun _ : Fin 2 ↦ (2 : ℝ)) := by
      ext j
      fin_cases j <;> simp [top, sx] <;> ring
    rw [htop_eq]
    exact hcombo
  -- A second interpolation between the two horizontal edges lands at the desired point.
  have hcombo :
      (1 - sy) • bottom + sy • top ∈ K := by
    exact hconv hbottom_mem htopEdge_mem (sub_nonneg.mpr hsy_le_one) hsy_nonneg (by ring)
  have hx_eq : x = (1 - sy) • bottom + sy • top := by
    ext j
    fin_cases j <;> simp [bottom, top, sy] <;> ring
  rw [hx_eq]
  exact hcombo

/-- Helper for Exercise 6.14: containing every nonnegative integer point forces `(1,1)` into the
interior. -/
lemma oneVector_mem_interior_of_containsAllNonnegativeIntegers
    {K : Set R2}
    (hconv : Convex ℝ K)
    (hints : ∀ n : Fin 2 → ℕ, (Nat.cast ∘ n : R2) ∈ K) :
    (fun _ : Fin 2 ↦ (1 : ℝ)) ∈ interior K := by
  have hsquare :
      Set.Icc (0 : R2) (fun _ ↦ (2 : ℝ)) ⊆ K :=
    twoSquare_subset_of_containsAllNonnegativeIntegers hconv hints
  have hball_subset : Metric.ball (fun _ : Fin 2 ↦ (1 : ℝ)) 1 ⊆ K := by
    intro u hu
    have hu_norm : ‖u - (fun _ : Fin 2 ↦ (1 : ℝ))‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hu
    have hu_square : u ∈ Set.Icc (0 : R2) (fun _ ↦ (2 : ℝ)) := by
      constructor
      · intro i
        have hi :
            ‖u i - 1‖ ≤ ‖u - (fun _ : Fin 2 ↦ (1 : ℝ))‖ := by
          simpa using norm_le_pi_norm (u - (fun _ : Fin 2 ↦ (1 : ℝ))) i
        have hi_lt : |u i - 1| < 1 := by
          simpa using lt_of_le_of_lt hi hu_norm
        have hbounds := abs_lt.mp hi_lt
        have hpos : 0 < u i := by
          linarith [hbounds.1]
        exact hpos.le
      · intro i
        have hi :
            ‖u i - 1‖ ≤ ‖u - (fun _ : Fin 2 ↦ (1 : ℝ))‖ := by
          simpa using norm_le_pi_norm (u - (fun _ : Fin 2 ↦ (1 : ℝ))) i
        have hi_lt : |u i - 1| < 1 := by
          simpa using lt_of_le_of_lt hi hu_norm
        have hbounds := abs_lt.mp hi_lt
        linarith [hbounds.2]
    exact hsquare hu_square
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (by simp)) hball_subset

/-- Helper for Exercise 6.14: a `ℤ_+^2`-free convex set misses at least one nonnegative integer
point. -/
lemma existsOutsideNonnegativeInteger_of_nonnegativeIntegerFree
    {K : Set R2}
    (hconv : Convex ℝ K)
    (hfree : is_nonnegative_integer_free K) :
    ∃ n : Fin 2 → ℕ, (Nat.cast ∘ n : R2) ∉ K := by
  by_contra hno
  push Not at hno
  have hone_int : (fun _ : Fin 2 ↦ (1 : ℝ)) ∈ interior K :=
    oneVector_mem_interior_of_containsAllNonnegativeIntegers hconv hno
  have hone_mem : (fun _ : Fin 2 ↦ (1 : ℝ)) ∈ ℤ_+^2 := by
    exact
      (mem_nonnegativeIntegerVectors_iff_exists).2
        ⟨fun _ : Fin 2 ↦ 1, by
          funext i
          simp⟩
  exact (is_nonnegative_integer_free.not_mem_interior hfree hone_mem) hone_int

/-- Helper for Exercise 6.14: if every genuinely new interior point of `L` lies in a patch that is
disjoint from `ℤ_+^2`, then `L` remains `ℤ_+^2`-free. -/
lemma isNonnegativeIntegerFree_of_interiorDiff_subset_openPatch
    {K L U : Set R2}
    (hKfree : is_nonnegative_integer_free K)
    (hnew : interior L \ interior K ⊆ U)
    (hUfree : Disjoint U (ℤ_+^2)) :
    is_nonnegative_integer_free L := by
  rw [is_nonnegative_integer_free_iff] at hKfree ⊢
  intro z hzL
  by_cases hzK : (Nat.cast ∘ z : R2) ∈ interior K
  · exact hKfree z hzK
  · have hzU : (Nat.cast ∘ z : R2) ∈ U := hnew ⟨hzL, hzK⟩
    have hzNonneg : (Nat.cast ∘ z : R2) ∈ ℤ_+^2 :=
      (mem_nonnegativeIntegerVectors_iff_exists).2 ⟨z, rfl⟩
    exact (Set.disjoint_left.mp hUfree) hzU hzNonneg

/-- Helper for Exercise 6.14: the ray from a point of `K` to an outside nonnegative integer
endpoint cannot lie in the lineality space of `K`. -/
lemma rayToOutsideNonnegativeInteger_not_mem_linealitySpace
    {K : Set R2}
    {x : R2}
    (hxK : x ∈ K)
    {n : Fin 2 → ℕ}
    (hnK : (Nat.cast ∘ n : R2) ∉ K) :
    x - (Nat.cast ∘ n : R2) ∉ linealitySpace K := by
  intro hr
  rw [mem_linealitySpace_iff] at hr
  have hn_mem : x + (-1 : ℝ) • (x - (Nat.cast ∘ n : R2)) ∈ K := hr hxK (-1)
  have hn_eq : x + (-1 : ℝ) • (x - (Nat.cast ∘ n : R2)) = (Nat.cast ∘ n : R2) := by
    ext i <;> simp
  exact hnK (hn_eq ▸ hn_mem)

/-- Helper for Exercise 6.14: a nonnegative frontier point in `ℝ²` either has a nonintegral
coordinate or is itself an embedded nonnegative integer vector. -/
lemma frontierPoint_nonintegral_or_nonnegativeInteger
    {b : R2}
    (hb_nonneg : 0 ≤ b) :
    (∃ i : Fin 2, b i ∉ Set.range (Int.cast : ℤ → ℝ)) ∨ b ∈ ℤ_+^2 := by
  -- In dimension two, either one coordinate is already nonintegral or both coordinates are
  -- nonnegative integers.
  by_cases h0 : b 0 ∈ Set.range (Int.cast : ℤ → ℝ)
  · by_cases h1 : b 1 ∈ Set.range (Int.cast : ℤ → ℝ)
    · right
      rw [mem_nonnegativeIntegerVectors_iff_forall]
      intro i
      fin_cases i
      · exact ⟨h0, hb_nonneg 0⟩
      · exact ⟨h1, hb_nonneg 1⟩
    · exact Or.inl ⟨1, h1⟩
  · exact Or.inl ⟨0, h0⟩

/-- Helper for Exercise 6.14: this three-facet region is the concrete maximal-free
counterexample used to audit the stated classification. -/
def nonnegativeIntegerFreeCounterexample : Set R2 :=
  {x | 0 ≤ x 0 + 2 * x 1 ∧ x 0 + 2 * x 1 ≤ 2 ∧ x 0 ≤ 1}

/-- Helper for Exercise 6.14: strict satisfaction of the three defining inequalities places a
point in the interior of the counterexample region. -/
lemma mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
    {x : R2}
    (hlower : 0 < x 0 + 2 * x 1)
    (hupper : x 0 + 2 * x 1 < 2)
    (hright : x 0 < 1) :
    x ∈ interior nonnegativeIntegerFreeCounterexample := by
  let U : Set R2 := {y | 0 < y 0 + 2 * y 1 ∧ y 0 + 2 * y 1 < 2 ∧ y 0 < 1}
  have hUOpen : IsOpen U := by
    -- Each strict affine inequality defines an open halfspace.
    have hlinear : Continuous fun y : R2 ↦ y 0 + 2 * y 1 := by
      fun_prop
    have hcoord : Continuous fun y : R2 ↦ y 0 := by
      fun_prop
    simpa only [U, Set.setOf_and] using
      (isOpen_lt continuous_const hlinear).inter
        ((isOpen_lt hlinear continuous_const).inter (isOpen_lt hcoord continuous_const))
  have hUSubset : U ⊆ nonnegativeIntegerFreeCounterexample := by
    intro y hy
    exact ⟨hy.1.le, hy.2.1.le, hy.2.2.le⟩
  -- The strict system is an open neighborhood contained in the closed region.
  exact interior_maximal hUSubset hUOpen ⟨hlower, hupper, hright⟩

/-- Helper for Exercise 6.14: the explicit three-facet counterexample region is convex. -/
lemma nonnegativeIntegerFreeCounterexample_convex :
    Convex ℝ nonnegativeIntegerFreeCounterexample := by
  intro x hx y hy a b ha hb hab
  simp only [nonnegativeIntegerFreeCounterexample, Set.mem_setOf_eq] at hx hy ⊢
  have hlowerX : 0 ≤ a * (x 0 + 2 * x 1) := mul_nonneg ha hx.1
  have hlowerY : 0 ≤ b * (y 0 + 2 * y 1) := mul_nonneg hb hy.1
  have hupperX : a * (x 0 + 2 * x 1) ≤ a * 2 :=
    mul_le_mul_of_nonneg_left hx.2.1 ha
  have hupperY : b * (y 0 + 2 * y 1) ≤ b * 2 :=
    mul_le_mul_of_nonneg_left hy.2.1 hb
  have hrightX : a * x 0 ≤ a * 1 := mul_le_mul_of_nonneg_left hx.2.2 ha
  have hrightY : b * y 0 ≤ b * 1 := mul_le_mul_of_nonneg_left hy.2.2 hb
  -- Distribute the convex combination through each of the three affine inequalities.
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  constructor
  · nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- Helper for Exercise 6.14: the explicit three-facet region has no nonnegative integer point
in its interior. -/
lemma nonnegativeIntegerFreeCounterexample_free :
    is_nonnegative_integer_free nonnegativeIntegerFreeCounterexample := by
  rw [is_nonnegative_integer_free_iff]
  intro z hz
  have hlowerValid :
      is_valid_inequality nonnegativeIntegerFreeCounterexample (![-1, -2] : R2) 0 := by
    intro x hx
    simp only [nonnegativeIntegerFreeCounterexample, Set.mem_setOf_eq] at hx
    simp [dotProduct, Fin.sum_univ_two]
    linarith [hx.1]
  have hupperValid :
      is_valid_inequality nonnegativeIntegerFreeCounterexample (![1, 2] : R2) 2 := by
    intro x hx
    simpa [nonnegativeIntegerFreeCounterexample, dotProduct, Fin.sum_univ_two] using hx.2.1
  have hrightValid :
      is_valid_inequality nonnegativeIntegerFreeCounterexample (![1, 0] : R2) 1 := by
    intro x hx
    simpa [nonnegativeIntegerFreeCounterexample, dotProduct, Fin.sum_univ_two] using hx.2.2
  have hlowerDot :=
    dotProduct_lt_of_memInterior_of_validInequality
      (by norm_num) hlowerValid hz
  have hupperDot :=
    dotProduct_lt_of_memInterior_of_validInequality
      (by norm_num) hupperValid hz
  have hrightDot :=
    dotProduct_lt_of_memInterior_of_validInequality
      (by norm_num) hrightValid hz
  have hlower : 0 < (z 0 : ℝ) + 2 * (z 1 : ℝ) := by
    simp [dotProduct, Fin.sum_univ_two] at hlowerDot
    linarith
  have hupper : (z 0 : ℝ) + 2 * (z 1 : ℝ) < 2 := by
    simpa [dotProduct, Fin.sum_univ_two] using hupperDot
  have hright : (z 0 : ℝ) < 1 := by
    simpa [dotProduct, Fin.sum_univ_two] using hrightDot
  have hz0lt : z 0 < 1 := by exact_mod_cast hright
  have hz0 : z 0 = 0 := by omega
  have hz1posReal : 0 < (z 1 : ℝ) := by
    simpa [hz0] using (half_pos hlower)
  have hz1ltReal : (z 1 : ℝ) < 1 := by
    rw [hz0] at hupper
    norm_num at hupper ⊢
    linarith
  have hz1pos : 0 < z 1 := by exact_mod_cast hz1posReal
  have hz1lt : z 1 < 1 := by exact_mod_cast hz1ltReal
  omega

/-- Helper for Exercise 6.14: one can move a positive distance from a point in any prescribed
direction while remaining in an open set. -/
lemma exists_pos_extrapolation_mem_open
    {U : Set R2}
    {z y : R2}
    (hU : IsOpen U)
    (hz : z ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ z + ε • (z - y) ∈ U := by
  have hcontinuous : Continuous fun ε : ℝ ↦ z + ε • (z - y) := by
    fun_prop
  have heventually :
      ∀ᶠ ε in nhds (0 : ℝ), z + ε • (z - y) ∈ U := by
    -- Continuity pulls the open neighborhood of `z` back to a neighborhood of zero.
    exact hcontinuous.continuousAt.eventually_mem (hU.mem_nhds (by simpa using hz))
  rcases Metric.eventually_nhds_iff.mp heventually with ⟨δ, hδ, hball⟩
  refine ⟨δ / 2, half_pos hδ, hball ?_⟩
  -- A positive half-radius lies in the neighborhood supplied by continuity.
  rw [Real.dist_eq]
  rw [sub_zero, abs_of_pos (half_pos hδ)]
  exact half_lt_self hδ

/-- Helper for Exercise 6.14: a convex enlargement containing an extrapolated interior point
must contain the original boundary point in its interior. -/
lemma mem_interior_of_extrapolatedInteriorPoint
    {L : Set R2}
    (hLconv : Convex ℝ L)
    {z y : R2}
    (hyL : y ∈ L)
    {ε : ℝ}
    (hε : 0 < ε)
    (hextrapolated : z + ε • (z - y) ∈ interior L) :
    z ∈ interior L := by
  let α : ℝ := 1 / (1 + ε)
  let β : ℝ := ε / (1 + ε)
  have hdenom : 0 < 1 + ε := by linarith
  have hα : 0 < α := by
    dsimp [α]
    positivity
  have hβ : 0 ≤ β := by
    dsimp [β]
    positivity
  have hsum : α + β = 1 := by
    dsimp [α, β]
    field_simp [hdenom.ne']
  have hcombo :=
    hLconv.combo_interior_self_mem_interior hextrapolated hyL hα hβ hsum
  have hcomboEq : α • (z + ε • (z - y)) + β • y = z := by
    -- The chosen barycentric coefficients undo the extrapolation exactly.
    ext i
    dsimp [α, β]
    change
      (1 / (1 + ε)) * (z i + ε * (z i - y i)) +
          (ε / (1 + ε)) * y i = z i
    field_simp [hdenom.ne']
    ring
  rwa [hcomboEq] at hcombo

/-- Helper for Exercise 6.14: the explicit three-facet region is maximal among convex
`ℤ_+^2`-free sets. -/
lemma nonnegativeIntegerFreeCounterexample_maximal :
    is_maximal_nonnegative_integer_free nonnegativeIntegerFreeCounterexample := by
  refine ⟨nonnegativeIntegerFreeCounterexample_convex,
    nonnegativeIntegerFreeCounterexample_free, ?_⟩
  intro L hKL hLconv hLfree
  apply Set.Subset.antisymm
  · intro y hyL
    by_contra hyK
    by_cases hlower : 0 ≤ y 0 + 2 * y 1
    · by_cases hupper : y 0 + 2 * y 1 ≤ 2
      · have hright : 1 < y 0 := by
          have : ¬ y 0 ≤ 1 := by
            intro hyRight
            exact hyK ⟨hlower, hupper, hyRight⟩
          exact lt_of_not_ge this
        let z : R2 := ![1, 0]
        let U : Set R2 := {v | 0 < v 0 + 2 * v 1 ∧ v 0 + 2 * v 1 < 2}
        have hlinear : Continuous fun v : R2 ↦ v 0 + 2 * v 1 := by
          fun_prop
        have hUOpen : IsOpen U := by
          -- The two strict slab inequalities form an open neighborhood of the facet witness.
          simpa only [U, Set.setOf_and] using
            (isOpen_lt continuous_const hlinear).inter
              (isOpen_lt hlinear continuous_const)
        have hzU : z ∈ U := by
          norm_num [z, U]
        rcases exists_pos_extrapolation_mem_open hUOpen hzU with
          ⟨ε, hε, hextrapolatedU⟩
        have hextrapolatedRight :
            (z + ε • (z - y)) 0 < 1 := by
          -- Crossing the vertical facet makes every positive extrapolation point inward.
          have hproduct : ε * (1 - y 0) < 0 :=
            mul_neg_of_pos_of_neg hε (sub_neg.mpr hright)
          simp only [z, Matrix.cons_val_zero, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
            smul_eq_mul]
          linarith
        have hextrapolatedInterior :
            z + ε • (z - y) ∈ interior nonnegativeIntegerFreeCounterexample := by
          rcases hextrapolatedU with ⟨hextrapolatedLower, hextrapolatedUpper⟩
          exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
            hextrapolatedLower hextrapolatedUpper hextrapolatedRight
        have hzInteriorL : z ∈ interior L :=
          mem_interior_of_extrapolatedInteriorPoint hLconv hyL hε
            (interior_mono hKL hextrapolatedInterior)
        have hzNonnegative : z ∈ ℤ_+^2 := by
          refine (mem_nonnegativeIntegerVectors_iff_exists).2 ⟨![1, 0], ?_⟩
          ext i
          fin_cases i <;> simp [z]
        exact (is_nonnegative_integer_free.not_mem_interior hLfree hzNonnegative) hzInteriorL
      · have hupper' : 2 < y 0 + 2 * y 1 := lt_of_not_ge hupper
        let z : R2 := ![0, 1]
        let U : Set R2 := {v | 0 < v 0 + 2 * v 1 ∧ v 0 < 1}
        have hlinear : Continuous fun v : R2 ↦ v 0 + 2 * v 1 := by
          fun_prop
        have hcoord : Continuous fun v : R2 ↦ v 0 := by
          fun_prop
        have hUOpen : IsOpen U := by
          -- The lower slab and right-hand inequalities are strict at the upper witness.
          simpa only [U, Set.setOf_and] using
            (isOpen_lt continuous_const hlinear).inter
              (isOpen_lt hcoord continuous_const)
        have hzU : z ∈ U := by
          norm_num [z, U]
        rcases exists_pos_extrapolation_mem_open hUOpen hzU with
          ⟨ε, hε, hextrapolatedU⟩
        have hextrapolatedUpper :
            (z + ε • (z - y)) 0 + 2 * (z + ε • (z - y)) 1 < 2 := by
          -- Crossing the upper slab facet makes every positive extrapolation point inward.
          have hproduct : ε * (2 - (y 0 + 2 * y 1)) < 0 :=
            mul_neg_of_pos_of_neg hε (sub_neg.mpr hupper')
          simp only [z, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.add_apply, Pi.smul_apply,
            Pi.sub_apply, smul_eq_mul]
          nlinarith
        have hextrapolatedInterior :
            z + ε • (z - y) ∈ interior nonnegativeIntegerFreeCounterexample := by
          rcases hextrapolatedU with ⟨hextrapolatedLower, hextrapolatedRight⟩
          exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
            hextrapolatedLower hextrapolatedUpper hextrapolatedRight
        have hzInteriorL : z ∈ interior L :=
          mem_interior_of_extrapolatedInteriorPoint hLconv hyL hε
            (interior_mono hKL hextrapolatedInterior)
        have hzNonnegative : z ∈ ℤ_+^2 := by
          refine (mem_nonnegativeIntegerVectors_iff_exists).2 ⟨![0, 1], ?_⟩
          ext i
          fin_cases i <;> simp [z]
        exact (is_nonnegative_integer_free.not_mem_interior hLfree hzNonnegative) hzInteriorL
    · have hlower' : y 0 + 2 * y 1 < 0 := lt_of_not_ge hlower
      let z : R2 := 0
      let U : Set R2 := {v | v 0 + 2 * v 1 < 2 ∧ v 0 < 1}
      have hlinear : Continuous fun v : R2 ↦ v 0 + 2 * v 1 := by
        fun_prop
      have hcoord : Continuous fun v : R2 ↦ v 0 := by
        fun_prop
      have hUOpen : IsOpen U := by
        -- The upper slab and right-hand inequalities are strict at the lower witness.
        simpa only [U, Set.setOf_and] using
          (isOpen_lt hlinear continuous_const).inter
            (isOpen_lt hcoord continuous_const)
      have hzU : z ∈ U := by
        norm_num [z, U]
      rcases exists_pos_extrapolation_mem_open hUOpen hzU with
        ⟨ε, hε, hextrapolatedU⟩
      have hextrapolatedLower :
          0 < (z + ε • (z - y)) 0 + 2 * (z + ε • (z - y)) 1 := by
        -- Crossing the lower slab facet makes every positive extrapolation point inward.
        have hproduct : 0 < ε * (-(y 0 + 2 * y 1)) :=
          mul_pos hε (neg_pos.mpr hlower')
        simp only [z, Pi.zero_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
        nlinarith
      have hextrapolatedInterior :
          z + ε • (z - y) ∈ interior nonnegativeIntegerFreeCounterexample := by
        rcases hextrapolatedU with ⟨hextrapolatedUpper, hextrapolatedRight⟩
        exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
          hextrapolatedLower hextrapolatedUpper hextrapolatedRight
      have hzInteriorL : z ∈ interior L :=
        mem_interior_of_extrapolatedInteriorPoint hLconv hyL hε
          (interior_mono hKL hextrapolatedInterior)
      have hzNonnegative : z ∈ ℤ_+^2 := by
        exact (mem_nonnegativeIntegerVectors_iff_exists).2 ⟨0, by funext i; simp [z]⟩
      exact (is_nonnegative_integer_free.not_mem_interior hLfree hzNonnegative) hzInteriorL
  · exact hKL

/-- Helper for Exercise 6.14: the integer point `(-1,1)` lies in the interior of the explicit
maximal `ℤ_+^2`-free region. -/
lemma nonnegativeIntegerFreeCounterexample_notLatticeFree :
    ¬ is_lattice_free nonnegativeIntegerFreeCounterexample := by
  intro hLatticeFree
  have hforbidden := (is_lattice_free_iff.mp hLatticeFree) (![-1, 1] : Fin 2 → ℤ)
  apply hforbidden
  -- All three defining inequalities are strict at `(-1,1)`.
  exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
    (by norm_num) (by norm_num) (by norm_num)

/-- Helper for Exercise 6.14: the explicit maximal-free region has an interior point in the
positive orthant. -/
lemma nonnegativeIntegerFreeCounterexample_meetsPositiveOrthant :
    ¬ Disjoint (interior nonnegativeIntegerFreeCounterexample) (Set.Ioi (0 : R2)) := by
  let p : R2 := fun _ ↦ 1 / 4
  have hpInterior : p ∈ interior nonnegativeIntegerFreeCounterexample := by
    -- The point `(1/4,1/4)` strictly satisfies all three facet inequalities.
    exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
      (by norm_num [p]) (by norm_num [p]) (by norm_num [p])
  have hpPositive : p ∈ Set.Ioi (0 : R2) := by
    constructor
    · intro i
      norm_num [p]
    · intro hpLe
      have hpZero := hpLe 0
      norm_num [p] at hpZero
  intro hDisjoint
  exact (Set.disjoint_left.mp hDisjoint) hpInterior hpPositive

/-- Helper for Exercise 6.14: the explicit maximal-free region cannot be one of the asserted
nonnegative supporting halfspaces. -/
lemma nonnegativeIntegerFreeCounterexample_not_supportingHalfspace :
    ¬ ∃ a : R2, 0 ≤ a ∧ a ≠ 0 ∧
      nonnegativeIntegerFreeCounterexample = nonnegative_supporting_halfspace a := by
  rintro ⟨a, haNonnegative, haNonzero, hEq⟩
  let p : R2 := fun _ ↦ 1 / 4
  have hpInterior : p ∈ interior nonnegativeIntegerFreeCounterexample := by
    exact mem_interior_nonnegativeIntegerFreeCounterexample_of_strict
      (by norm_num [p]) (by norm_num [p]) (by norm_num [p])
  have hpInteriorHalfspace : p ∈ interior (nonnegative_supporting_halfspace a) := by
    rwa [← hEq]
  have hpDotNegative : dotProduct a p < 0 := by
    simpa [interior_nonnegativeSupportingHalfspace_eq haNonzero] using hpInteriorHalfspace
  have hpNonnegative : 0 ≤ p := by
    intro i
    norm_num [p]
  -- Nonnegative vectors have nonnegative dot product, contradicting halfspace interiority.
  exact (not_lt_of_ge (dotProduct_nonneg_of_nonneg haNonnegative hpNonnegative)) hpDotNegative

/-- Helper for Exercise 6.14: the proposed equivalence is false at the explicit three-facet
maximal `ℤ_+^2`-free set. -/
lemma maximalNonnegativeIntegerFree_notLatticeFree_classification_false :
    ¬ (is_maximal_nonnegative_integer_free nonnegativeIntegerFreeCounterexample ∧
        ¬ is_lattice_free nonnegativeIntegerFreeCounterexample ↔
      ∃ a : R2, 0 ≤ a ∧ a ≠ 0 ∧
        nonnegativeIntegerFreeCounterexample = nonnegative_supporting_halfspace a) := by
  intro hClassification
  have hHalfspace := hClassification.mp
    ⟨nonnegativeIntegerFreeCounterexample_maximal,
      nonnegativeIntegerFreeCounterexample_notLatticeFree⟩
  exact nonnegativeIntegerFreeCounterexample_not_supportingHalfspace hHalfspace

/-- Helper for Exercise 6.14: maximal nonnegative-integer-freeness and failure of ordinary
lattice-freeness do not universally force disjointness from the strict positive orthant. -/
lemma not_forall_disjoint_strictPositiveOrthant :
    ¬ ∀ K : Set R2,
      is_maximal_nonnegative_integer_free K →
        ¬ is_lattice_free K → Disjoint (interior K) (Set.Ioi (0 : R2)) := by
  intro hDisjoint
  -- Specializing the proposed principle to the explicit three-facet region contradicts its
  -- verified positive interior point.
  exact nonnegativeIntegerFreeCounterexample_meetsPositiveOrthant
    (hDisjoint nonnegativeIntegerFreeCounterexample
      nonnegativeIntegerFreeCounterexample_maximal
      nonnegativeIntegerFreeCounterexample_notLatticeFree)

/-- Helper for remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_14.lean:
a coordinate unit strip is also disjoint from the embedded nonnegative integer lattice. -/
lemma coordinateUnitStrip_disjoint_nonnegativeIntegerVectors
    (i : Fin q)
    (a : ℝ) :
    Disjoint (coordinateUnitStrip i a) (ℤ_+^q) := by
  -- Restrict the imported integer-strip disjointness along `ℤ_+^q ⊆ ℤ^q`.
  rw [Set.disjoint_left]
  intro u huU huNonnegative
  exact
    (Set.disjoint_left.mp (coordinateUnitStrip_disjoint_integerVectors i a)) huU
      (nonnegativeIntegerVectors_subset_integerVectors huNonnegative)

/-- Helper for Exercise 6.14: the proposed universal disjointness principle for maximal
`ℤ_+^2`-free, non-lattice-free sets is false. -/
lemma disjoint_strictPositiveOrthant_of_maximalNonnegativeIntegerFree
    ¬ ∀ K : Set R2,
      is_maximal_nonnegative_integer_free K →
        ¬ is_lattice_free K → Disjoint (interior K) (Set.Ioi (0 : R2)) := by
  exact not_forall_disjoint_strictPositiveOrthant

/-- Helper for Exercise 6.14: each standard basis vector lies in the positive cone `Set.Ioi 0`
for the product order on `ℝ²`. -/
lemma standardBasis_mem_positiveOrthant
    (i : Fin 2) :
    Pi.single i (1 : ℝ) ∈ Set.Ioi (0 : R2) := by
  -- In the product order, `0 < eᵢ` means `eᵢ` is coordinatewise nonnegative and not zero.
  constructor
  · intro j
    by_cases hji : j = i
    · subst hji
      simp [Pi.single]
    · simp [Pi.single, hji]
  · intro hle
    have : (1 : ℝ) ≤ 0 := by
      simpa [Pi.single] using hle i
    linarith

/-- Helper for Exercise 6.14: positive multiples of a standard basis vector stay in `Set.Ioi 0`.
-/
lemma positiveMultiple_standardBasis_mem_positiveOrthant
    {i : Fin 2}
    {t : ℝ}
    (ht : 0 < t) :
    t • Pi.single i (1 : ℝ) ∈ Set.Ioi (0 : R2) := by
  -- Positive scaling preserves coordinatewise nonnegativity and keeps the vector nonzero.
  constructor
  · intro j
    by_cases hji : j = i
    · subst hji
      simp [Pi.single, ht.le]
    · simp [Pi.single, hji]
  · intro hle
    have : t ≤ 0 := by
      simpa [Pi.single] using hle i
    linarith

/-- Helper for Exercise 6.14: a continuous linear functional on `ℝ²` is the dot product with its
values on the standard basis. -/
lemma continuousLinearMap_eq_dotProduct_basisValues
    (f : R2 →L[ℝ] ℝ) :
    ∀ x : R2, f x = dotProduct (fun i ↦ f (Pi.single i 1)) x := by
  intro x
  have hx :
      x = x 0 • Pi.single 0 (1 : ℝ) + x 1 • Pi.single 1 (1 : ℝ) := by
    -- Expanding coordinates against the two basis vectors reduces the claim to linearity.
    ext i
    fin_cases i <;> simp
  calc
    f x = x 0 * f (Pi.single 0 (1 : ℝ)) + x 1 * f (Pi.single 1 (1 : ℝ)) := by
      -- Rewrite `x` in the standard basis and apply linearity coordinatewise.
      rw [hx]
      simp [map_add, map_smul, smul_eq_mul]
    _ = dotProduct (fun i ↦ f (Pi.single i 1)) x := by
      simp [dotProduct, Fin.sum_univ_two, mul_comm]

/-- Helper for Exercise 6.14: separating `interior K` from the strict positive orthant yields a
nonzero nonnegative normal whose supporting halfspace contains `K`. -/
lemma separatorVector_of_disjointStrictPositiveOrthant
    {K : Set R2}
    (hconv : Convex ℝ K)
    (hclosed : IsClosed K)
    (hinterior : (interior K).Nonempty)
    (hdisj : Disjoint (interior K) (Set.Ioi (0 : R2))) :
    ∃ a : R2, 0 ≤ a ∧ a ≠ 0 ∧ K ⊆ nonnegative_supporting_halfspace a := by
  have _hclosed : IsClosed K := hclosed
  -- Route correction: in the current Lean target `Set.Ioi (0 : R2)` is the positive cone for the
  -- product order, so the standard basis vectors and their positive multiples are available
  -- separation witnesses.
  have horthConvex : Convex ℝ (Set.Ioi (0 : R2)) := by
    simpa using convex_Ioi (0 : R2)
  have horthNonempty : (Set.Ioi (0 : R2)).Nonempty :=
    ⟨Pi.single 0 (1 : ℝ), standardBasis_mem_positiveOrthant 0⟩
  have hsep :
      ∃ (f : R2 →L[ℝ] ℝ) (u : ℝ),
        f ≠ 0 ∧ (∀ x ∈ K, f x ≤ u) ∧ ∀ x ∈ Set.Ioi (0 : R2), u ≤ f x := by
    simpa using
      geometric_hahn_banach_of_nonempty_interior hconv horthConvex hdisj hinterior horthNonempty
  rcases hsep with ⟨f, u, hfne, hKle, horth_le⟩
  let a : R2 := fun i ↦ f (Pi.single i 1)
  have hrepr : ∀ x : R2, f x = dotProduct a x := by
    -- Repackage the separating functional by its basis coefficients.
    intro x
    simpa [a] using continuousLinearMap_eq_dotProduct_basisValues f x
  have ha_nonneg : 0 ≤ a := by
    intro i
    -- A negative basis coefficient would violate the lower bound on sufficiently large positive
    -- multiples of that basis vector.
    by_contra hneg
    let t : ℝ := (|u| + 1) / (-a i)
    have ht_pos : 0 < t := by
      dsimp [t]
      have hai_neg : a i < 0 := not_le.mp hneg
      have : 0 < -a i := by linarith
      exact div_pos (by positivity) this
    have ht_mem : t • Pi.single i (1 : ℝ) ∈ Set.Ioi (0 : R2) :=
      positiveMultiple_standardBasis_mem_positiveOrthant ht_pos
    have hu_le : u ≤ f (t • Pi.single i (1 : ℝ)) := horth_le _ ht_mem
    have hai_ne : a i ≠ 0 := by
      have hai_neg : a i < 0 := not_le.mp hneg
      exact ne_of_lt hai_neg
    have hcalc : f (t • Pi.single i (1 : ℝ)) = -(|u| + 1) := by
      -- Choosing `t` forces the `i`-th basis value to drive the functional strictly below `u`.
      calc
        f (t • Pi.single i (1 : ℝ)) = t * a i := by
          simp [a, map_smul, smul_eq_mul]
        _ = -(|u| + 1) := by
          dsimp [t]
          field_simp [hai_ne]
    have hu_lt : -(|u| + 1) < u := by
      have habs : -|u| ≤ u := neg_abs_le u
      linarith
    exact (not_lt_of_ge hu_le) (by simpa [hcalc] using hu_lt)
  have ha_ne : a ≠ 0 := by
    -- If every basis coefficient vanished, then the separating functional itself would vanish.
    intro ha_zero
    apply hfne
    ext x
    simpa [ha_zero] using hrepr x
  have hu_nonpos : u ≤ 0 := by
    by_contra hu_pos
    have hu_pos' : 0 < u := not_le.mp hu_pos
    obtain ⟨i, hi_ne⟩ : ∃ i, a i ≠ 0 := by
      by_contra hzero
      apply ha_ne
      ext i
      by_contra hi_zero
      exact hzero ⟨i, hi_zero⟩
    have hi_pos : 0 < a i := lt_of_le_of_ne (ha_nonneg i) (Ne.symm hi_ne)
    let ε : ℝ := u / (2 * a i)
    have hεpos : 0 < ε := by
      dsimp [ε]
      exact div_pos hu_pos' (by positivity)
    have hε_mem : ε • Pi.single i (1 : ℝ) ∈ Set.Ioi (0 : R2) :=
      positiveMultiple_standardBasis_mem_positiveOrthant hεpos
    have hu_le : u ≤ f (ε • Pi.single i (1 : ℝ)) := horth_le _ hε_mem
    have hcalc : f (ε • Pi.single i (1 : ℝ)) = u / 2 := by
      -- Scaling a positive basis vector downward pushes the separating lower bound below itself.
      calc
        f (ε • Pi.single i (1 : ℝ)) = ε * a i := by
          simp [a, map_smul, smul_eq_mul]
        _ = u / 2 := by
          dsimp [ε]
          field_simp [hi_ne]
    have : u ≤ u / 2 := by
      simpa [hcalc] using hu_le
    linarith
  refine ⟨a, ha_nonneg, ha_ne, ?_⟩
  intro x hx
  -- The separating inequality on `K` collapses to the supporting halfspace once `u ≤ 0`.
  have hxle : f x ≤ 0 := (hKle x hx).trans hu_nonpos
  simpa [nonnegative_supporting_halfspace, hrepr x] using hxle

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap06/section_6_5/ch6_sec6_5_exercise_6_14.lean -/
theorem maximal_nonnegative_integer_free_not_lattice_free_iff
    {K : Set R2} :
    (∃ a : R2, a ∈ Set.Ici (0 : R2) \ {0} ∧ K = nonnegative_supporting_halfspace a) →
      is_maximal_nonnegative_integer_free K ∧ ¬ is_lattice_free K := by
  rintro ⟨a, ha_mem, rfl⟩
  have ha_nonneg : 0 ≤ a := ha_mem.1
  have ha : a ≠ 0 := by
    simpa using ha_mem.2
  -- The verified halfspace side of Exercise 6.14 is the only universal implication supported by
  -- the checked geometry in this file.
  exact nonnegativeSupportingHalfspace_maximal_and_notLatticeFree ha_nonneg ha

end Exercise614
