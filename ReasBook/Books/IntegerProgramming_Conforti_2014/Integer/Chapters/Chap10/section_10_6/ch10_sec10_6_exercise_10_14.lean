import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_8.ch3_sec3_8_definition_3_8_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_7.ch7_sec7_7_exercise_7_19
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

-- This item contains the source-facing relaxation and its odd-cycle validity proof.

-- This exercise reuses the Chapter 7 stable-set and odd-cycle owners
-- `stableSetIndicator`, `is_valid_inequality`, `CycleSupport`, `odd_cycle_inequality_rhs`, and
-- `fractional_stable_set_polytope`, while keeping the source-facing cone owner on arbitrary
-- vertex types and bridging the `Fin n` specialization to the canonical Section 10.3 owner
-- `N(FRAC(G))`.

open scoped LovaszSchrijverNotation

section Exercise_10_14

variable {V : Type}
variable (G : SimpleGraph V)

/-- The homogenized cone over `FRAC(G)` consists of the vectors `(x₀, x)` with
`0 ≤ x_v ≤ x₀` for every vertex and `x_u + x_v ≤ x₀` on every graph edge. -/
def fractional_stable_set_cone : Set (Option V → ℝ) :=
  {z |
    0 ≤ z none ∧
      (∀ v : V, 0 ≤ z (some v) ∧ z (some v) ≤ z none) ∧
        ∀ ⦃u v : V⦄, G.Adj u v → z (some u) + z (some v) ≤ z none}

/-- Membership in `fractional_stable_set_cone G` is exactly the homogenized
`FRAC(G)` inequality system. -/
theorem mem_fractional_stable_set_cone_iff
    (z : Option V → ℝ) :
    z ∈ fractional_stable_set_cone G ↔
      0 ≤ z none ∧
        (∀ v : V, 0 ≤ z (some v) ∧ z (some v) ≤ z none) ∧
          ∀ ⦃u v : V⦄, G.Adj u v → z (some u) + z (some v) ≤ z none :=
  Iff.rfl

/-- A point of `FRAC(G)` gives the normalized homogenized vector `(1, x)` in
`fractional_stable_set_cone G`. -/
theorem homogenized_point_mem_fractional_stable_set_cone
    {x : V → ℝ}
    (hx : x ∈ FRAC(G)) :
    (fun i ↦ match i with
      | none => 1
      | some v => x v) ∈ fractional_stable_set_cone G := by
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hx_box, hx_edge⟩
  rw [mem_fractional_stable_set_cone_iff]
  refine ⟨zero_le_one, ?_⟩
  refine ⟨?_, ?_⟩
  · intro v
    simpa using hx_box v
  · intro u v huv
    simpa using hx_edge huv

/-- A normalized point of `fractional_stable_set_cone G` dehomogenizes to a point of `FRAC(G)`.
-/
theorem mem_fractional_stable_set_polytope_of_mem_fractional_stable_set_cone
    {z : Option V → ℝ}
    (hz : z ∈ fractional_stable_set_cone G)
    (hz₀ : z none = 1) :
    (fun v ↦ z (some v)) ∈ FRAC(G) := by
  rw [mem_fractional_stable_set_cone_iff] at hz
  rcases hz with ⟨-, hz_box, hz_edge⟩
  rw [mem_fractional_stable_set_polytope_iff]
  refine ⟨?_, ?_⟩
  · intro v
    constructor
    · exact (hz_box v).1
    · -- Normalization turns the cone's scaled upper bound into the unit bound.
      simpa [hz₀] using (hz_box v).2
  · intro u v huv
    simpa [hz₀] using hz_edge huv

/-- The Lovász-Schrijver relaxation `N(FRAC(G))` consists of the vectors `x : V → ℝ` for which
there exists a symmetric matrix `Y` indexed by `Option V` with `Y none none = 1`,
`Y e₀ = diag(Y)`, and whose `v`-columns `Y e_v` together with the difference columns
`Y (e₀ - e_v)` all lie in the homogenized cone over `FRAC(G)`. -/
def lovasz_schrijver_n_frac_relaxation : Set (V → ℝ) :=
  {x | ∃ Y : Matrix (Option V) (Option V) ℝ,
      Y.IsSymm ∧
      Y none none = 1 ∧
      (∀ i : Option V, Y i none = Y i i) ∧
      (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      (∀ v : V, (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      ∀ v : V, x v = Y (some v) none}

/-- Membership in `lovasz_schrijver_n_frac_relaxation G` is exactly the existence of a symmetric
matrix witness with the diagonal/first-column relation and the cone constraints defining
`N(FRAC(G))`. -/
theorem mem_lovasz_schrijver_n_frac_relaxation_iff
    (x : V → ℝ) :
    x ∈ lovasz_schrijver_n_frac_relaxation G ↔
      ∃ Y : Matrix (Option V) (Option V) ℝ,
        Y.IsSymm ∧
        Y none none = 1 ∧
        (∀ i : Option V, Y i none = Y i i) ∧
        (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        (∀ v : V, (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        ∀ v : V, x v = Y (some v) none :=
  Iff.rfl

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: the fractional stable-set
relaxation is convex. -/
private lemma convex_fractionalStableSetPolytope
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    Convex ℝ (FRAC(G)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_fractional_stable_set_polytope_iff] at hx hy ⊢
  rcases hx with ⟨hxBox, hxEdge⟩
  rcases hy with ⟨hyBox, hyEdge⟩
  refine ⟨?_, ?_⟩
  · intro v
    constructor
    · -- Convex combinations preserve coordinate nonnegativity.
      change 0 ≤ a * x v + b * y v
      nlinarith [(hxBox v).1, (hyBox v).1]
    · -- The equation `a + b = 1` preserves the unit upper bound.
      change a * x v + b * y v ≤ 1
      nlinarith [(hxBox v).2, (hyBox v).2, hab]
  · intro u v huv
    -- The edge inequalities are affine and hence survive the same combination.
    change a * x u + b * y u + (a * x v + b * y v) ≤ 1
    nlinarith [hxEdge huv, hyEdge huv, hab]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: membership in the homogenized
cone over `FRAC(G)` is equivalent to the scaled box-and-edge system. -/
private lemma mem_homogenizedCone_fractionalStableSetPolytope_iff
    {n : ℕ} (G : SimpleGraph (Fin n)) (y : Fin (n + 1) → ℝ) :
    y ∈ homogenized_cone (FRAC(G)) ↔
      0 ≤ y 0 ∧
        (∀ v : Fin n, 0 ≤ y v.succ ∧ y v.succ ≤ y 0) ∧
          ∀ {u v : Fin n}, G.Adj u v → y u.succ + y v.succ ≤ y 0 := by
  constructor
  · intro hy
    rw [mem_homogenized_cone_iff] at hy
    rcases hy with ⟨t, ht, x, hxHull, rfl⟩
    have hx : x ∈ FRAC(G) := by
      rwa [convexHull_eq_self.2 (convex_fractionalStableSetPolytope G)] at hxHull
    rw [mem_fractional_stable_set_polytope_iff] at hx
    rcases hx with ⟨hxBox, hxEdge⟩
    refine ⟨?_, ?_, ?_⟩
    · -- The leading coordinate is precisely the nonnegative cone scale.
      simpa [homogenized_point] using ht
    · intro v
      constructor
      · simpa [homogenized_point] using mul_nonneg ht (hxBox v).1
      · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hxBox v).2 ht
    · intro u v huv
      -- Scale the edge inequality by the nonnegative cone coefficient.
      simpa [homogenized_point, mul_add, add_comm, add_left_comm, add_assoc,
        mul_comm, mul_left_comm, mul_assoc] using
        mul_le_mul_of_nonneg_left (hxEdge huv) ht
  · rintro ⟨hyZero, hyBox, hyEdge⟩
    by_cases hzero : y 0 = 0
    · -- At scale zero the box constraints force the whole vector to vanish.
      have hyTail (v : Fin n) : y v.succ = 0 := by
        have hv := hyBox v
        rw [hzero] at hv
        linarith
      have hyEq : y = 0 := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [hzero]
        · intro v
          simpa using hyTail v
      let x : Fin n → ℝ := 0
      have hx : x ∈ FRAC(G) := by
        rw [mem_fractional_stable_set_polytope_iff]
        refine ⟨?_, ?_⟩
        · intro v
          simp [x]
        · intro u v huv
          simp [x]
      rw [mem_homogenized_cone_iff]
      refine ⟨0, le_rfl, x, subset_convexHull ℝ _ hx, ?_⟩
      simp [hyEq]
    · -- At positive scale, divide the tail coordinates by the leading coordinate.
      have hyPos : 0 < y 0 := lt_of_le_of_ne hyZero (Ne.symm hzero)
      let x : Fin n → ℝ := fun v ↦ y v.succ / y 0
      have hx : x ∈ FRAC(G) := by
        rw [mem_fractional_stable_set_polytope_iff]
        refine ⟨?_, ?_⟩
        · intro v
          constructor
          · exact div_nonneg (hyBox v).1 hyZero
          · exact (div_le_one hyPos).2 (hyBox v).2
        · intro u v huv
          rw [← add_div]
          exact (div_le_one hyPos).2 (hyEdge huv)
      rw [mem_homogenized_cone_iff]
      refine ⟨y 0, hyZero, x, subset_convexHull ℝ _ hx, ?_⟩
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [homogenized_point]
      · intro v
        simp only [Pi.smul_apply, smul_eq_mul, homogenized_point, Fin.cons_succ, x]
        field_simp

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: reindexing along
`finSuccEquiv` identifies the explicit graph cone with the canonical homogenized cone. -/
private lemma mem_fractionalStableSetCone_iff_reindex_mem_homogenizedCone
    {n : ℕ} (G : SimpleGraph (Fin n)) (z : Option (Fin n) → ℝ) :
    z ∈ fractional_stable_set_cone G ↔
      (fun i : Fin (n + 1) ↦ z (finSuccEquiv n i)) ∈ homogenized_cone (FRAC(G)) := by
  -- Both sides reduce to the same scaled box-and-edge inequalities.
  rw [mem_fractional_stable_set_cone_iff,
    mem_homogenizedCone_fractionalStableSetPolytope_iff]
  simp

/-- For graphs already presented on `Fin n`, the source-facing `Option`-indexed definition of
`N(FRAC(G))` agrees with the canonical Section 10.3 Lovász-Schrijver owner. -/
theorem lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    lovasz_schrijver_n_frac_relaxation G = N(FRAC(G)) := by
  classical
  ext x
  rw [mem_lovasz_schrijver_n_frac_relaxation_iff, mem_lovasz_schrijver_N_iff]
  constructor
  · rintro ⟨Y, hSymm, hTop, hDiag, hColumn, hResidual, hx⟩
    let Y' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.reindex (finSuccEquiv n).symm (finSuccEquiv n).symm Y
    have hFirst : Matrix.mulVec Y' (lifted_basis 0) = homogenized_point x := by
      -- The reindexed first column is exactly `(1, x)`.
      ext i
      refine Fin.cases ?_ ?_ i
      · simpa [Y', mulVec_lifted_basis, homogenized_point] using hTop
      · intro v
        simpa [Y', mulVec_lifted_basis, homogenized_point] using (hx v).symm
    have hxFrac : x ∈ FRAC(G) := by
      rw [mem_fractional_stable_set_polytope_iff]
      refine ⟨?_, ?_⟩
      · intro v
        have hCol := (mem_fractional_stable_set_cone_iff G
          (fun i ↦ Y i (some v))).1 (hColumn v)
        have hRes := (mem_fractional_stable_set_cone_iff G
          (fun i ↦ Y i none - Y i (some v))).1 (hResidual v)
        have hEntrySymm : Y none (some v) = Y (some v) none := by
          simpa [Matrix.transpose_apply] using
            congr_fun (congr_fun hSymm (some v)) none
        constructor
        · rw [hx v]
          exact (hCol.2.1 v).1.trans_eq (hDiag (some v)).symm
        · rw [hx v]
          have hTopResidual := hRes.1
          rw [hTop, hEntrySymm] at hTopResidual
          linarith
      · intro u v huv
        have hCol := (mem_fractional_stable_set_cone_iff G
          (fun i ↦ Y i (some u))).1 (hColumn u)
        have hRes := (mem_fractional_stable_set_cone_iff G
          (fun i ↦ Y i none - Y i (some u))).1 (hResidual u)
        have hCrossNonneg : 0 ≤ Y (some v) (some u) := (hCol.2.1 v).1
        have hCrossNonpos : Y (some v) (some u) ≤ 0 := by
          have hEdge := hCol.2.2 huv
          have hEntrySymm : Y none (some u) = Y (some u) none := by
            simpa [Matrix.transpose_apply] using
              congr_fun (congr_fun hSymm (some u)) none
          rw [← hDiag (some u), hEntrySymm] at hEdge
          linarith
        have hCross : Y (some v) (some u) = 0 := le_antisymm hCrossNonpos hCrossNonneg
        have hResidualBound := (hRes.2.1 v).2
        have hEntrySymm : Y none (some u) = Y (some u) none := by
          simpa [Matrix.transpose_apply] using
            congr_fun (congr_fun hSymm (some u)) none
        rw [hCross, hTop, hEntrySymm, ← hx u, ← hx v] at hResidualBound
        linarith
    refine ⟨Y', ?_, hFirst⟩
    rw [isLovaszSchrijverMatrix_iff]
    refine ⟨hSymm.reindex _, ?_, ?_, ?_⟩
    · -- The normalized first column belongs to the canonical cone.
      rw [hFirst]
      exact homogenized_point_mem_homogenized_cone _ (subset_convexHull ℝ _ hxFrac)
    · intro v
      constructor
      · rw [mulVec_lifted_basis]
        simpa [Y'] using
          (mem_fractionalStableSetCone_iff_reindex_mem_homogenizedCone G
            (fun i ↦ Y i (some v))).1 (hColumn v)
      · rw [Matrix.mulVec_sub, mulVec_lifted_basis, mulVec_lifted_basis]
        simpa [Y'] using
          (mem_fractionalStableSetCone_iff_reindex_mem_homogenizedCone G
            (fun i ↦ Y i none - Y i (some v))).1 (hResidual v)
    · intro v
      simpa [Y'] using (hDiag (some v)).symm
  · rintro ⟨Y, hY, hFirst⟩
    rw [isLovaszSchrijverMatrix_iff] at hY
    rcases hY with ⟨hSymm, hColumnZero, hColumns, hDiag⟩
    let Y' : Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
      Matrix.reindex (finSuccEquiv n) (finSuccEquiv n) Y
    refine ⟨Y', Matrix.IsSymm.reindex hSymm _, ?_, ?_, ?_, ?_, ?_⟩
    · -- The first canonical column fixes the top-left entry at one.
      simpa [Y', mulVec_lifted_basis, homogenized_point] using
        congrArg (fun z ↦ z 0) hFirst
    · intro i
      rcases i with _ | v
      · rfl
      · simpa [Y'] using (hDiag v).symm
    · intro v
      apply (mem_fractionalStableSetCone_iff_reindex_mem_homogenizedCone G _).2
      simpa [Y', mulVec_lifted_basis] using (hColumns v).1
    · intro v
      apply (mem_fractionalStableSetCone_iff_reindex_mem_homogenizedCone G _).2
      simpa [Y', Matrix.mulVec_sub, mulVec_lifted_basis] using (hColumns v).2
    · intro v
      simpa [Y', mulVec_lifted_basis, homogenized_point] using
        (congrArg (fun z ↦ z v.succ) hFirst).symm

/-- For graphs on `Fin n`, membership in the local source-facing `Option`-indexed owner is exactly
membership in the canonical Section 10.3 relaxation `N(FRAC(G))`. -/
theorem mem_lovasz_schrijver_n_frac_relaxation_iff_mem_lovasz_schrijver_N
    {n : ℕ} (G : SimpleGraph (Fin n)) {x : Fin n → ℝ} :
    x ∈ lovasz_schrijver_n_frac_relaxation G ↔ x ∈ N(FRAC(G)) := by
  rw [lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N G]

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: an odd initial segment splits
into its first term and consecutive pairs. -/
private lemma sum_range_two_mul_add_one
    (q : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range (2 * q + 1), a i =
      a 0 + ∑ k ∈ Finset.range q, (a (2 * k + 1) + a (2 * k + 2)) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have hlength : 2 * (q + 1) + 1 = (2 * q + 1) + 2 := by omega
      rw [hlength, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      ring

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: an odd segment of length
`2 * r + 3` splits into its two endpoints and the intervening consecutive pairs. -/
private lemma sum_range_two_mul_add_three
    (r : ℕ) (a : ℕ → ℝ) :
    ∑ i ∈ Finset.range (2 * r + 3), a i =
      a 0 + a 1 +
        (∑ k ∈ Finset.range r, (a (2 * k + 2) + a (2 * k + 3))) +
          a (2 * r + 2) := by
  induction r with
  | zero => simp [Finset.sum_range_succ]
  | succ r ih =>
      have hlength : 2 * (r + 1) + 3 = (2 * r + 3) + 2 := by omega
      rw [hlength, Finset.sum_range_succ, Finset.sum_range_succ, ih,
        Finset.sum_range_succ]
      simp only [Nat.mul_add, Nat.mul_one]
      ring

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: pairing the remaining
vertices of an odd cycle bounds a nonnegative cyclic sum when one entry is zero or the common edge
upper bound. -/
private lemma oddRangeSum_le_of_eq_zero_or_top
    (m q : ℕ) (hm : m = 2 * q + 1) (hq : 0 < q)
    (a : ℕ → ℝ) (t : ℝ)
    (haNonneg : ∀ k < m, 0 ≤ a k)
    (haAdjacent : ∀ k, k + 1 < m → a k + a (k + 1) ≤ t)
    (haWrap : a (m - 1) + a 0 ≤ t)
    (haEndpoint : a 0 = 0 ∨ a 0 = t) :
    ∑ k ∈ Finset.range m, a k ≤ (q : ℝ) * t := by
  rcases haEndpoint with haZero | haTop
  · -- When the first entry vanishes, pair all remaining entries consecutively.
    have hPairBound :
        ∑ k ∈ Finset.range q, (a (2 * k + 1) + a (2 * k + 2)) ≤
          ∑ _k ∈ Finset.range q, t := by
      refine Finset.sum_le_sum ?_
      intro k hk
      apply haAdjacent
      have hkLt : k < q := Finset.mem_range.mp hk
      omega
    have hPairBound' :
        ∑ k ∈ Finset.range q, (a (2 * k + 1) + a (2 * k + 2)) ≤
          (q : ℝ) * t := by
      simpa [nsmul_eq_mul] using hPairBound
    have hsplit := sum_range_two_mul_add_one q a
    rw [← hm] at hsplit
    rw [hsplit, haZero]
    simpa using hPairBound'
  · -- When the first entry is maximal, its two cyclic neighbors vanish; pair the interior.
    rcases q with _ | r
    · omega
    · have haOne : a 1 = 0 := by
        have honeLt : 1 < m := by omega
        have hbound := haAdjacent 0 honeLt
        have hnonneg := haNonneg 1 honeLt
        rw [haTop] at hbound
        linarith
      have haLast : a (2 * r + 2) = 0 := by
        have hlastIndex : m - 1 = 2 * r + 2 := by omega
        have hlastLt : m - 1 < m := by omega
        have hnonneg := haNonneg (m - 1) hlastLt
        rw [hlastIndex] at hnonneg
        rw [hlastIndex, haTop] at haWrap
        linarith
      have hPairBound :
          ∑ k ∈ Finset.range r, (a (2 * k + 2) + a (2 * k + 3)) ≤
            ∑ _k ∈ Finset.range r, t := by
        refine Finset.sum_le_sum ?_
        intro k hk
        apply haAdjacent
        have hkLt : k < r := Finset.mem_range.mp hk
        omega
      have hPairBound' :
          ∑ k ∈ Finset.range r, (a (2 * k + 2) + a (2 * k + 3)) ≤
            (r : ℝ) * t := by
        simpa [nsmul_eq_mul] using hPairBound
      have hsplit := sum_range_two_mul_add_three r a
      have hlength : m = 2 * r + 3 := by omega
      rw [← hlength] at hsplit
      rw [hsplit, haTop, haOne, haLast]
      calc
        t + 0 +
              (∑ k ∈ Finset.range r, (a (2 * k + 2) + a (2 * k + 3))) + 0
            ≤ t + (r : ℝ) * t := by linarith
        _ = ((r + 1 : ℕ) : ℝ) * t := by
          push_cast
          ring

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: every cycle support has a
canonical index at its zeroth labelled vertex. -/
private lemma cycleSupportLength_pos (C : CycleSupport V) :
    0 < C.length := by
  -- A cycle support has at least three labelled vertices.
  have hthree : 3 ≤ C.length := C.length_ge_three
  omega

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: the canonical zeroth index of
a cycle support. -/
private def cycleSupportZeroIndex (C : CycleSupport V) : Fin C.length :=
  ⟨0, cycleSupportLength_pos C⟩

/-- Helper for remote integer-programming proof cleanup
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean: a vector in the fractional
stable-set cone obeys the scaled odd-cycle inequality when its zeroth cycle coordinate is zero or
its homogenizing coordinate. -/
private lemma fractionalStableSetCone_cycleSum_le_of_zero_or_top
    (C : CycleSupport V) (hC : C.IsContainedIn G) (hodd : Odd C.length)
    (z : Option V → ℝ) (hz : z ∈ fractional_stable_set_cone G)
    (hzEndpoint :
      z (some (C.verts (cycleSupportZeroIndex C))) = 0 ∨
        z (some (C.verts (cycleSupportZeroIndex C))) = z none) :
    C.vertexFinset.sum (fun v ↦ z (some v)) ≤
      odd_cycle_inequality_rhs C * z none := by
  classical
  rw [mem_fractional_stable_set_cone_iff] at hz
  rcases hz with ⟨hzTop, hzBox, hzEdge⟩
  rcases hodd.exists_bit1 with ⟨q, hlength⟩
  have hq : 0 < q := by
    have hthree := C.length_ge_three
    omega
  let a : ℕ → ℝ := fun k ↦
    if hk : k < C.length then z (some (C.verts ⟨k, hk⟩)) else 0
  have haNonneg : ∀ k < C.length, 0 ≤ a k := by
    intro k hk
    simpa [a, hk] using (hzBox (C.verts ⟨k, hk⟩)).1
  have haAdjacent : ∀ k, k + 1 < C.length → a k + a (k + 1) ≤ z none := by
    intro k hkNext
    have hk : k < C.length := by omega
    let i : Fin C.length := ⟨k, hk⟩
    let j : Fin C.length := ⟨k + 1, hkNext⟩
    have hnext :
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (cycleSupportLength_pos C)⟩ = j := by
      apply Fin.ext
      simp [i, j, Nat.mod_eq_of_lt hkNext]
    have hedge := hC i
    rw [hnext] at hedge
    simpa [a, hk, hkNext, i, j] using hzEdge hedge
  have haWrap : a (C.length - 1) + a 0 ≤ z none := by
    have hlast : C.length - 1 < C.length := by omega
    let i : Fin C.length := ⟨C.length - 1, hlast⟩
    have hnext :
        ⟨(i.1 + 1) % C.length,
          Nat.mod_lt _ (cycleSupportLength_pos C)⟩ = cycleSupportZeroIndex C := by
      apply Fin.ext
      have hsucc : C.length - 1 + 1 = C.length := by omega
      simp [i, cycleSupportZeroIndex, hsucc]
    have hedge := hC i
    rw [hnext] at hedge
    simpa [a, hlast, cycleSupportZeroIndex, cycleSupportLength_pos, i] using hzEdge hedge
  have haEndpoint : a 0 = 0 ∨ a 0 = z none := by
    simpa [a, cycleSupportZeroIndex, cycleSupportLength_pos] using hzEndpoint
  have hRange := oddRangeSum_le_of_eq_zero_or_top C.length q hlength hq a (z none)
    haNonneg haAdjacent haWrap haEndpoint
  have hFinSum :
      (∑ i : Fin C.length, z (some (C.verts i))) =
        ∑ k ∈ Finset.range C.length, a k := by
    rw [Finset.sum_fin_eq_sum_range]
  have hVertexSum :
      C.vertexFinset.sum (fun v ↦ z (some v)) =
        ∑ i : Fin C.length, z (some (C.verts i)) := by
    rw [CycleSupport.vertexFinset, CyclicSupport.vertexFinset, Finset.sum_map]
  have hRhs : odd_cycle_inequality_rhs C = (q : ℝ) := by
    rw [odd_cycle_inequality_rhs_eq]
    have hhalf : (C.length - 1) / 2 = q := by omega
    rw [hhalf]
  rw [hVertexSum, hFinSum, hRhs]
  exact hRange

section Validity

variable [Fintype V]

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_14.lean
Exercise 10.14. If `C` is an odd cycle support contained in `G`, then the odd-cycle inequality
`∑_{j ∈ V(C)} x_j ≤ (|C| - 1) / 2` is valid for `N(FRAC(G))`. -/
theorem odd_cycle_inequality_valid_for_lovasz_schrijver_n_frac
    (C : CycleSupport V)
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    is_valid_inequality
      (lovasz_schrijver_n_frac_relaxation G)
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := by
  classical
  rw [is_valid_inequality_iff]
  intro x hx
  rw [mem_lovasz_schrijver_n_frac_relaxation_iff] at hx
  rcases hx with ⟨Y, hSymm, hTop, hDiag, hColumn, hResidual, hxFirst⟩
  let i₀ : Fin C.length := cycleSupportZeroIndex C
  let v₀ : V := C.verts i₀
  have hEntrySymm : Y none (some v₀) = Y (some v₀) none := by
    simpa [Matrix.transpose_apply] using
      congr_fun (congr_fun hSymm (some v₀)) none
  have hColumnEndpoint : Y (some v₀) (some v₀) = Y none (some v₀) := by
    calc
      Y (some v₀) (some v₀) = Y (some v₀) none := (hDiag (some v₀)).symm
      _ = Y none (some v₀) := hEntrySymm.symm
  have hColumnBound :
      C.vertexFinset.sum (fun v ↦ Y (some v) (some v₀)) ≤
        odd_cycle_inequality_rhs C * Y none (some v₀) := by
    -- The selected column has its selected cycle coordinate equal to its cone scale.
    apply fractionalStableSetCone_cycleSum_le_of_zero_or_top G C hC hodd
      (fun i ↦ Y i (some v₀)) (hColumn v₀)
    exact Or.inr hColumnEndpoint
  have hResidualEndpoint :
      Y (some v₀) none - Y (some v₀) (some v₀) = 0 := by
    rw [hDiag (some v₀)]
    ring
  have hResidualBound :
      C.vertexFinset.sum (fun v ↦ Y (some v) none - Y (some v) (some v₀)) ≤
        odd_cycle_inequality_rhs C * (Y none none - Y none (some v₀)) := by
    -- The residual column vanishes at the selected cycle coordinate.
    apply fractionalStableSetCone_cycleSum_le_of_zero_or_top G C hC hodd
      (fun i ↦ Y i none - Y i (some v₀)) (hResidual v₀)
    exact Or.inl hResidualEndpoint
  have hSumColumns :
      C.vertexFinset.sum (fun v ↦ Y (some v) (some v₀)) +
          C.vertexFinset.sum (fun v ↦ Y (some v) none - Y (some v) (some v₀)) =
        C.vertexFinset.sum x := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [hxFirst v]
    ring
  -- Adding the column and residual estimates recovers the represented point.
  rw [stableSetIndicator_dotProduct]
  rw [← hSumColumns]
  calc
    C.vertexFinset.sum (fun v ↦ Y (some v) (some v₀)) +
          C.vertexFinset.sum (fun v ↦ Y (some v) none - Y (some v) (some v₀)) ≤
        odd_cycle_inequality_rhs C * Y none (some v₀) +
          odd_cycle_inequality_rhs C * (Y none none - Y none (some v₀)) :=
      add_le_add hColumnBound hResidualBound
    _ = odd_cycle_inequality_rhs C := by
      rw [hTop]
      ring

/-- For graphs on `Fin n`, Exercise 10.14 can be stated directly on the canonical Section 10.3
Lovász-Schrijver relaxation `N(FRAC(G))`. -/
theorem odd_cycle_inequality_valid_for_lovasz_schrijver_N_frac
    {n : ℕ} (G : SimpleGraph (Fin n))
    (C : CycleSupport (Fin n))
    (hC : C.IsContainedIn G)
    (hodd : Odd C.length) :
    is_valid_inequality
      (N(FRAC(G)))
      (stableSetIndicator C.vertexFinset)
      (odd_cycle_inequality_rhs C) := by
  simpa [lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N G] using
    odd_cycle_inequality_valid_for_lovasz_schrijver_n_frac G C hC hodd

#print axioms odd_cycle_inequality_valid_for_lovasz_schrijver_n_frac

end Validity

end Exercise_10_14
