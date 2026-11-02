import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_6.ch10_sec10_6_exercise_10_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap10.section_10_3.ch10_sec10_3_1_lemma_10_7

open scoped LovaszSchrijverNotation

-- This exercise reuses the Chapter 7 graph-support owners together with the source-facing
-- `fractional_stable_set_cone G` and `lovasz_schrijver_n_frac_relaxation G` owners from
-- Exercise 10.14. The source-facing `Option V` witness surface is kept here for arbitrary finite
-- vertex types, and the `Fin n` specialization is bridged below to the canonical Section 10.3
-- owner `N₊(FRAC(G))`.

section Exercise_10_15

variable {V : Type}

noncomputable local instance : DecidableEq V := Classical.decEq V

section SourceOwner

variable [Fintype V]
variable (G : SimpleGraph V)

/-- The positive-semidefinite Lovasz-Schrijver relaxation `N₊(FRAC(G))`, stated directly on the
ambient vertex type `V` through an `Option V`-indexed lifted matrix witness whose columns and
residual columns lie in `fractional_stable_set_cone G`. -/
def lovasz_schrijver_nplus_frac_relaxation : Set (V → ℝ) :=
  {x | ∃ Y : Matrix (Option V) (Option V) ℝ,
      Y.PosSemidef ∧
      Y none none = 1 ∧
      (∀ i : Option V, Y i none = Y i i) ∧
      (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      (∀ v : V,
        (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
      ∀ v : V, x v = Y (some v) none}

end SourceOwner

variable (G : SimpleGraph V)

/-- Membership in `lovasz_schrijver_nplus_frac_relaxation G` is exactly the existence of the
standard positive-semidefinite lifted witness for `N₊(FRAC(G))`. -/
theorem mem_lovasz_schrijver_nplus_frac_relaxation_iff
    {x : V → ℝ} :
    x ∈ lovasz_schrijver_nplus_frac_relaxation G ↔
      ∃ Y : Matrix (Option V) (Option V) ℝ,
        Y.PosSemidef ∧
        Y none none = 1 ∧
        (∀ i : Option V, Y i none = Y i i) ∧
        (∀ v : V, (fun i : Option V ↦ Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        (∀ v : V,
          (fun i : Option V ↦ Y i none - Y i (some v)) ∈ fractional_stable_set_cone G) ∧
        ∀ v : V, x v = Y (some v) none :=
  Iff.rfl

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: the fractional stable-set
relaxation is convex. -/
private lemma convex_fractionalStableSetPolytopeForNplus
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    Convex ℝ (FRAC(G)) := by
  intro x hx y hy a b ha hb hab
  rw [mem_fractional_stable_set_polytope_iff] at hx hy ⊢
  rcases hx with ⟨hxBox, hxEdge⟩
  rcases hy with ⟨hyBox, hyEdge⟩
  refine ⟨?_, ?_⟩
  · intro v
    constructor
    · -- Nonnegativity is preserved coordinatewise by a convex combination.
      change 0 ≤ a * x v + b * y v
      nlinarith [(hxBox v).1, (hyBox v).1]
    · -- The affine coefficient identity preserves the unit upper bound.
      change a * x v + b * y v ≤ 1
      nlinarith [(hxBox v).2, (hyBox v).2, hab]
  · intro u v huv
    -- The edge inequality is affine in the two coordinates.
    change a * x u + b * y u + (a * x v + b * y v) ≤ 1
    nlinarith [hxEdge huv, hyEdge huv, hab]

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: a vector in the canonical
homogenized cone satisfies the scaled fractional stable-set inequalities. -/
private lemma homogenizedConeFractionalStableSetDataForNplus
    {n : ℕ} (G : SimpleGraph (Fin n)) {y : Fin (n + 1) → ℝ}
    (hy : y ∈ homogenized_cone (FRAC(G))) :
    0 ≤ y 0 ∧
      (∀ v : Fin n, 0 ≤ y v.succ ∧ y v.succ ≤ y 0) ∧
      ∀ ⦃u v : Fin n⦄, G.Adj u v → y u.succ + y v.succ ≤ y 0 := by
  rw [mem_homogenized_cone_iff] at hy
  rcases hy with ⟨t, ht, x, hxHull, rfl⟩
  have hx : x ∈ FRAC(G) := by
    rwa [convexHull_eq_self.2 (convex_fractionalStableSetPolytopeForNplus G)] at hxHull
  rw [mem_fractional_stable_set_polytope_iff] at hx
  rcases hx with ⟨hxBox, hxEdge⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [homogenized_point] using ht
  · intro v
    constructor
    · simpa [homogenized_point] using mul_nonneg ht (hxBox v).1
    · simpa [homogenized_point] using mul_le_mul_of_nonneg_left (hxBox v).2 ht
  · intro u v huv
    -- Scaling the edge inequality yields its homogeneous form.
    simpa [homogenized_point, mul_add, add_comm, add_left_comm, add_assoc,
      mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left (hxEdge huv) ht

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: reindexing along
`finSuccEquiv` identifies the source-facing graph cone with the canonical homogenized cone. -/
private lemma mem_fractionalStableSetCone_reindex_iff
    {n : ℕ} (G : SimpleGraph (Fin n)) (z : Option (Fin n) → ℝ) :
    z ∈ fractional_stable_set_cone G ↔
      (fun i : Fin (n + 1) ↦ z (finSuccEquiv n i)) ∈ homogenized_cone (FRAC(G)) := by
  constructor
  · intro hz
    rw [mem_fractional_stable_set_cone_iff] at hz
    rcases hz with ⟨hzTop, hzBox, hzEdge⟩
    by_cases hzero : z none = 0
    · -- At scale zero, every tail coordinate vanishes, so the reindexed vector is zero.
      have hzTail (v : Fin n) : z (some v) = 0 := by
        have hv := hzBox v
        rw [hzero] at hv
        linarith
      have hreindex : (fun i : Fin (n + 1) ↦ z (finSuccEquiv n i)) = 0 := by
        funext i
        refine Fin.cases ?_ ?_ i
        · simp [hzero]
        · intro v
          simpa using hzTail v
      rw [mem_homogenized_cone_iff]
      refine ⟨0, le_rfl, (0 : Fin n → ℝ), ?_, ?_⟩
      · exact subset_convexHull ℝ _ <| by
          rw [mem_fractional_stable_set_polytope_iff]
          simp
      · simp [hreindex]
    · -- At positive scale, divide the tail by the top coordinate and rehomogenize it.
      have hzPos : 0 < z none := lt_of_le_of_ne hzTop (Ne.symm hzero)
      let x : Fin n → ℝ := fun v ↦ z (some v) / z none
      have hx : x ∈ FRAC(G) := by
        rw [mem_fractional_stable_set_polytope_iff]
        refine ⟨?_, ?_⟩
        · intro v
          exact ⟨div_nonneg (hzBox v).1 hzTop, (div_le_one hzPos).2 (hzBox v).2⟩
        · intro u v huv
          rw [← add_div]
          exact (div_le_one hzPos).2 (hzEdge huv)
      rw [mem_homogenized_cone_iff]
      refine ⟨z none, hzTop, x, subset_convexHull ℝ _ hx, ?_⟩
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [homogenized_point]
      · intro v
        simp only [Pi.smul_apply, smul_eq_mul, homogenized_point, Fin.cons_succ, x,
          finSuccEquiv_succ]
        field_simp
  · intro hz
    -- The canonical cone data become exactly the source-facing box and edge inequalities.
    have hdata := homogenizedConeFractionalStableSetDataForNplus G hz
    rw [mem_fractional_stable_set_cone_iff]
    simpa using hdata

/-- For graphs already presented on `Fin n`, the source-facing `Option`-indexed definition of
`N₊(FRAC(G))` agrees with the canonical Section 10.3 Lovász-Schrijver owner. -/
theorem lovasz_schrijver_nplus_frac_relaxation_eq_lovasz_schrijver_N_plus
    {n : ℕ} (G : SimpleGraph (Fin n)) :
    lovasz_schrijver_nplus_frac_relaxation G = N₊(FRAC(G)) := by
  classical
  ext x
  rw [mem_lovasz_schrijver_nplus_frac_relaxation_iff,
    mem_lovasz_schrijver_N_plus_iff]
  constructor
  · rintro ⟨Y, hYpsd, hTop, hDiag, hColumn, hResidual, hx⟩
    let Y' : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
      Matrix.reindex (finSuccEquiv n).symm (finSuccEquiv n).symm Y
    have hSymm : Y.IsSymm := by
      simpa using hYpsd.isHermitian
    have hxLinear : x ∈ lovasz_schrijver_n_frac_relaxation G :=
      ⟨Y, hSymm, hTop, hDiag, hColumn, hResidual, hx⟩
    have hxCanonical : x ∈ N(FRAC(G)) := by
      rw [← lovasz_schrijver_n_frac_relaxation_eq_lovasz_schrijver_N G]
      exact hxLinear
    have hxFrac : x ∈ FRAC(G) :=
      lovasz_schrijver_N_subset _ (convex_fractionalStableSetPolytopeForNplus G) hxCanonical
    have hFirst : Matrix.mulVec Y' (lifted_basis 0) = homogenized_point x := by
      -- The reindexed first column is the normalized lift `(1, x)`.
      ext i
      refine Fin.cases ?_ ?_ i
      · simpa [Y', mulVec_lifted_basis, homogenized_point] using hTop
      · intro v
        simpa [Y', mulVec_lifted_basis, homogenized_point] using (hx v).symm
    refine ⟨Y', ?_, ?_, hFirst⟩
    · rw [isLovaszSchrijverMatrix_iff]
      refine ⟨hSymm.reindex _, ?_, ?_, ?_⟩
      · rw [hFirst]
        exact homogenized_point_mem_homogenized_cone _ (subset_convexHull ℝ _ hxFrac)
      · intro v
        constructor
        · rw [mulVec_lifted_basis]
          simpa [Y'] using
            (mem_fractionalStableSetCone_reindex_iff G
              (fun i ↦ Y i (some v))).1 (hColumn v)
        · rw [Matrix.mulVec_sub, mulVec_lifted_basis, mulVec_lifted_basis]
          simpa [Y'] using
            (mem_fractionalStableSetCone_reindex_iff G
              (fun i ↦ Y i none - Y i (some v))).1 (hResidual v)
      · intro v
        simpa [Y'] using (hDiag (some v)).symm
    · -- Positive semidefiniteness is invariant under the equivalence reindexing.
      simpa [Y', Matrix.reindex_apply] using hYpsd.submatrix (finSuccEquiv n)
  · rintro ⟨Y, hY, hYpsd, hFirst⟩
    rw [isLovaszSchrijverMatrix_iff] at hY
    rcases hY with ⟨hSymm, -, hColumns, hDiag⟩
    let Y' : Matrix (Option (Fin n)) (Option (Fin n)) ℝ :=
      Matrix.reindex (finSuccEquiv n) (finSuccEquiv n) Y
    refine ⟨Y', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Pulling the canonical PSD witness back preserves positive semidefiniteness.
      simpa [Y', Matrix.reindex_apply] using hYpsd.submatrix (finSuccEquiv n).symm
    · simpa [Y', mulVec_lifted_basis, homogenized_point] using
        congrArg (fun z ↦ z 0) hFirst
    · intro i
      rcases i with _ | v
      · rfl
      · simpa [Y'] using (hDiag v).symm
    · intro v
      apply (mem_fractionalStableSetCone_reindex_iff G _).2
      simpa [Y', mulVec_lifted_basis] using (hColumns v).1
    · intro v
      apply (mem_fractionalStableSetCone_reindex_iff G _).2
      simpa [Y', Matrix.mulVec_sub, mulVec_lifted_basis] using (hColumns v).2
    · intro v
      simpa [Y', mulVec_lifted_basis, homogenized_point] using
        (congrArg (fun z ↦ z v.succ) hFirst).symm

/-- For graphs on `Fin n`, membership in the local source-facing `Option`-indexed owner is exactly
membership in the canonical Section 10.3 relaxation `N₊(FRAC(G))`. -/
theorem mem_lovasz_schrijver_nplus_frac_relaxation_iff_mem_lovasz_schrijver_N_plus
    {n : ℕ} (G : SimpleGraph (Fin n)) {x : Fin n → ℝ} :
    x ∈ lovasz_schrijver_nplus_frac_relaxation G ↔ x ∈ N₊(FRAC(G)) := by
  rw [lovasz_schrijver_nplus_frac_relaxation_eq_lovasz_schrijver_N_plus G]

/-- The positive-semidefinite relaxation `N₊(FRAC(G))` is contained in the corresponding linear
Lovasz-Schrijver relaxation `N(FRAC(G))`. -/
theorem lovasz_schrijver_nplus_frac_relaxation_subset_n_frac_relaxation :
    lovasz_schrijver_nplus_frac_relaxation G ⊆ lovasz_schrijver_n_frac_relaxation G := by
  intro x hx
  rcases hx with ⟨Y, hYpsd, hY00, hdiag, hcols, hres, hxY⟩
  exact ⟨Y, by simpa using hYpsd.isHermitian, hY00, hdiag, hcols, hres, hxY⟩

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: a cyclic offset is the
value of the corresponding subtraction in `Fin`. -/
private lemma cyclicOffset_eq_subValForNplus {m : ℕ} [NeZero m] (i j : Fin m) :
    cyclic_offset i j = (j - i).1 := by
  -- Split at the linear wrap point and normalize both sides to the same natural difference.
  rw [cyclic_offset_eq]
  by_cases hij : i ≤ j
  · rw [show j.1 + m - i.1 = (j.1 - i.1) + m by omega, Nat.add_mod_right,
      Fin.sub_val_of_le hij]
    exact Nat.mod_eq_of_lt (by omega)
  · have hij' : j < i := lt_of_not_ge hij
    have hsub : (j - i).1 = m + j.1 - i.1 :=
      (Fin.coe_sub_iff_lt (a := j) (b := i)).2 hij'
    have hmod_lt : j.1 + m - i.1 < m := by omega
    rw [Nat.mod_eq_of_lt hmod_lt]
    omega

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: cyclic offset zero
identifies its two endpoints. -/
private lemma cyclicOffset_eq_zero_iff_forNplus {m : ℕ} [NeZero m] (i j : Fin m) :
    cyclic_offset i j = 0 ↔ i = j := by
  -- In the additive group `Fin m`, subtraction vanishes exactly on the diagonal.
  rw [cyclicOffset_eq_subValForNplus]
  constructor
  · intro h
    have hsub : j - i = 0 := Fin.ext h
    exact (sub_eq_zero.mp hsub).symm
  · rintro rfl
    simp

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: cyclic offset one is the
successor relation generated by `finRotate`. -/
private lemma cyclicOffset_eq_one_iff_forNplus {m : ℕ} [NeZero m]
    (hm : 2 ≤ m) (i j : Fin m) :
    cyclic_offset i j = 1 ↔ j = finRotate m i := by
  -- Translate the numerical offset into addition by one in `Fin m`.
  rw [cyclicOffset_eq_subValForNplus]
  constructor
  · intro h
    have hone : (j - i : Fin m) = 1 := by
      apply Fin.ext
      simpa [Fin.val_one', Nat.mod_eq_of_lt hm] using h
    have hadd := congrArg (fun z : Fin m ↦ z + i) hone
    simpa [finRotate_apply, add_comm] using hadd
  · rintro rfl
    rw [finRotate_apply, add_comm, add_sub_cancel_right]
    simp [Nat.mod_eq_of_lt hm]

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: relative to a fixed
antihole vertex, its predecessor and successor are adjacent, and every other distinct labelled
vertex is adjacent to the center. -/
private lemma antiholeCenterNeighborhood
    (H : AntiholeSupport V) (hH : H.IsContainedIn G) (j : Fin H.length) :
    G.Adj (H.verts ((finRotate H.length).symm j))
        (H.verts (finRotate H.length j)) ∧
      ∀ i : Fin H.length,
        i ≠ j →
        i ≠ (finRotate H.length).symm j →
        i ≠ finRotate H.length j →
        G.Adj (H.verts j) (H.verts i) := by
  have hlen_pos : 0 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  -- Local instance justification (finite cyclic arithmetic): positivity is the only missing
  -- input needed to interpret subtraction in `Fin H.length`.
  letI : NeZero H.length := ⟨Nat.ne_of_gt hlen_pos⟩
  have htwo : 2 ≤ H.length := le_trans (by decide) H.length_ge_five
  have hone_lt : 1 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  have htwo_lt : 2 < H.length := lt_of_lt_of_le (by decide) H.length_ge_five
  have hpredSuccOffsets :
      2 ≤ cyclic_offset ((finRotate H.length).symm j) (finRotate H.length j) ∧
        2 ≤ cyclic_offset (finRotate H.length j) ((finRotate H.length).symm j) := by
    rw [cyclicOffset_eq_subValForNplus, cyclicOffset_eq_subValForNplus,
      finRotate_apply, finRotate_symm_apply]
    constructor
    · rw [show j + 1 - (j - 1) = (1 + 1 : Fin H.length) by abel]
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hone_lt]
      rw [Nat.mod_eq_of_lt htwo_lt]
    · rw [show j - 1 - (j + 1) = -(1 + 1 : Fin H.length) by abel]
      rw [Fin.val_neg', Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hone_lt]
      rw [Nat.mod_eq_of_lt htwo_lt]
      rw [Nat.mod_eq_of_lt (Nat.sub_lt hlen_pos (by decide : 0 < 2))]
      exact Nat.le_sub_of_add_le <| le_trans (by decide : 2 + 2 ≤ 5) H.length_ge_five
  have hpredSuccNe : (finRotate H.length).symm j ≠ finRotate H.length j := by
    intro heq
    have hoffZero :
        cyclic_offset ((finRotate H.length).symm j) (finRotate H.length j) = 0 :=
      (cyclicOffset_eq_zero_iff_forNplus _ _).2 heq
    omega
  refine ⟨hH _ _ hpredSuccNe hpredSuccOffsets.1 hpredSuccOffsets.2, ?_⟩
  intro i hij hipred hisucc
  have hforwardZero : cyclic_offset j i ≠ 0 := by
    simpa [cyclicOffset_eq_zero_iff_forNplus] using hij.symm
  have hforwardOne : cyclic_offset j i ≠ 1 := by
    intro hone
    exact hisucc ((cyclicOffset_eq_one_iff_forNplus htwo j i).1 hone)
  have hbackwardZero : cyclic_offset i j ≠ 0 := by
    simpa [cyclicOffset_eq_zero_iff_forNplus] using hij
  have hbackwardOne : cyclic_offset i j ≠ 1 := by
    intro hone
    have hrot : j = finRotate H.length i :=
      (cyclicOffset_eq_one_iff_forNplus htwo i j).1 hone
    exact hipred <| by
      apply (finRotate H.length).injective
      simpa using hrot.symm
  apply hH j i hij.symm
  · omega
  · omega

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: a fractional stable-set
cone vector saturated at an antihole vertex has support sum at most twice its homogenizing
coordinate. -/
private lemma fractionalStableSetCone_antiholeSum_le_two_mul_top
    (H : AntiholeSupport V) (hH : H.IsContainedIn G) (j : Fin H.length)
    (z : Option V → ℝ)
    (hz : z ∈ fractional_stable_set_cone G)
    (hcenter : z (some (H.verts j)) = z none) :
    H.vertexFinset.sum (fun v ↦ z (some v)) ≤ 2 * z none := by
  have hcone := (mem_fractional_stable_set_cone_iff G z).1 hz
  have hneighbors := antiholeCenterNeighborhood (G := G) H hH j
  let p : Fin H.length := (finRotate H.length).symm j
  let s : Fin H.length := finRotate H.length j
  have hsucc_ne : s ≠ j := by
    exact Equiv.Perm.mem_support.mp <| by
      simp [support_finRotate_of_le (le_trans (by decide : 2 ≤ 5) H.length_ge_five)]
  have hpred_ne : p ≠ j := by
    intro hpj
    have hfixed : j = s := by
      calc
        j = finRotate H.length p := by
          exact (Equiv.apply_symm_apply (finRotate H.length) j).symm
        _ = finRotate H.length j := congrArg (finRotate H.length) hpj
        _ = s := rfl
    exact hsucc_ne hfixed.symm
  have hpred_succ_ne : p ≠ s := by
    intro hps
    have hloop : G.Adj (H.verts p) (H.verts p) := by
      simpa [p, s, hps] using hneighbors.1
    exact G.loopless.irrefl _ hloop
  have hfar_zero (i : Fin H.length)
      (hij : i ≠ j) (hip : i ≠ p) (his : i ≠ s) :
      z (some (H.verts i)) = 0 := by
    have hadj : G.Adj (H.verts j) (H.verts i) := by
      exact hneighbors.2 i hij (by simpa [p] using hip) (by simpa [s] using his)
    have hedge := hcone.2.2 hadj
    have hiNonneg := (hcone.2.1 (H.verts i)).1
    rw [hcenter] at hedge
    linarith
  have hlabelSum :
      (∑ i : Fin H.length, z (some (H.verts i))) =
        ∑ i ∈ ({p, j, s} : Finset (Fin H.length)), z (some (H.verts i)) := by
    -- Every term outside the center/predecessor/successor triple vanishes.
    symm
    refine Finset.sum_subset (Finset.subset_univ _) ?_
    intro i hi hnot
    have hip : i ≠ p := by
      intro hip
      exact hnot (by simp [hip])
    have hij : i ≠ j := by
      intro hij
      exact hnot (by simp [hij])
    have his : i ≠ s := by
      intro his
      exact hnot (by simp [his])
    exact hfar_zero i hij hip his
  have htriple :
      (∑ i ∈ ({p, j, s} : Finset (Fin H.length)), z (some (H.verts i))) ≤
        2 * z none := by
    have hedge := hcone.2.2 hneighbors.1
    rw [show (finRotate H.length).symm j = p by rfl,
      show finRotate H.length j = s by rfl] at hedge
    rw [Finset.sum_insert (by simp [hpred_ne, hpred_succ_ne]),
      Finset.sum_insert (by simpa using hsucc_ne.symm), Finset.sum_singleton]
    rw [hcenter]
    linarith
  rw [AntiholeSupport.vertexFinset, CyclicSupport.vertexFinset, Finset.sum_map,
    hlabelSum]
  exact htriple

/-- Helper for remote integer-programming proof completion
Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean: in a normalized positive
semidefinite matrix, the square of a first-column sum is bounded by the sum of the corresponding
principal block. -/
private lemma sum_firstColumn_sq_le_principalSum_of_posSemidef
    (S : Finset V) (Y : Matrix (Option V) (Option V) ℝ)
    (hYpsd : Y.PosSemidef) (hTop : Y none none = 1) :
    (S.sum (fun v ↦ Y (some v) none)) ^ 2 ≤
      S.sum (fun j ↦ S.sum (fun i ↦ Y (some i) (some j))) := by
  let a : ℝ := S.sum (fun v ↦ Y (some v) none)
  let e : Option ↑S → Option V := fun
    | none => none
    | some v => some v.1
  let A : Matrix (Option ↑S) (Option ↑S) ℝ := Y.submatrix e e
  let w : Option ↑S → ℝ := fun
    | none => -a
    | some _ => 1
  have hSymm : Y.IsSymm := by
    simpa using hYpsd.isHermitian
  have hEntrySymm (v : V) : Y none (some v) = Y (some v) none := by
    simpa [Matrix.transpose_apply] using
      congr_fun (congr_fun hSymm (some v)) none
  have sum_subtype (f : V → ℝ) : (∑ v : ↑S, f v.1) = S.sum f := by
    -- Normalize every subtype-indexed sum through `S.attach` once.
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach S f
  have hsumSymm : ∑ v : ↑S, Y none (some v.1) = a := by
    calc
      ∑ v : ↑S, Y none (some v.1) = S.sum (fun v ↦ Y none (some v)) :=
        by simpa only using sum_subtype (fun v ↦ Y none (some v))
      _ = S.sum (fun v ↦ Y (some v) none) := by
        apply Finset.sum_congr rfl
        intro v hv
        exact hEntrySymm v
      _ = a := rfl
  have hApsd : A.PosSemidef := by
    -- Restricting to the selected principal block preserves positive semidefiniteness.
    simpa [A] using hYpsd.submatrix e
  have hmul_none : (A.mulVec w) none = 0 := by
    -- The top row cancels because its selected entries sum to `a`.
    rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
    simp only [A, e, w, Matrix.submatrix_apply, mul_one]
    rw [hTop, hsumSymm]
    ring
  have hmul_some (i : ↑S) :
      (A.mulVec w) (some i) =
        -a * Y (some i.1) none + S.sum (fun j ↦ Y (some i.1) (some j)) := by
    -- A selected lower row splits into its first-column term and its selected block row.
    rw [Matrix.mulVec, dotProduct, Fintype.sum_option]
    simp only [A, e, w, Matrix.submatrix_apply, mul_one]
    rw [sum_subtype (fun j ↦ Y (some i.1) (some j))]
    ring
  have hnonneg : 0 ≤ dotProduct w (A.mulVec w) := by
    -- Evaluate positive semidefiniteness on the vector `(-a, 1, …, 1)`.
    simpa using hApsd.dotProduct_mulVec_nonneg w
  have hquad :
      dotProduct w (A.mulVec w) =
        -a * a + S.sum (fun j ↦ S.sum (fun i ↦ Y (some i) (some j))) := by
    calc
      dotProduct w (A.mulVec w) = ∑ i : ↑S, (A.mulVec w) (some i) := by
        rw [dotProduct, Fintype.sum_option, hmul_none]
        simp [w]
      _ = ∑ i : ↑S,
          (-a * Y (some i.1) none + S.sum (fun j ↦ Y (some i.1) (some j))) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hmul_some i
      _ = S.sum (fun i ↦
          -a * Y (some i) none + S.sum (fun j ↦ Y (some i) (some j))) := by
        simpa only using sum_subtype (fun i ↦
          -a * Y (some i) none + S.sum (fun j ↦ Y (some i) (some j)))
      _ = -a * a + S.sum (fun i ↦ S.sum (fun j ↦ Y (some i) (some j))) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      _ = -a * a + S.sum (fun j ↦ S.sum (fun i ↦ Y (some i) (some j))) := by
        rw [Finset.sum_comm]
  rw [hquad] at hnonneg
  change a ^ 2 ≤ _
  nlinarith

/-- remote integer-programming proof completion Integer/Chapters/Chap10/section_10_6/ch10_sec10_6_exercise_10_15.lean
Exercise 10.15. For every odd antihole support `H` contained in `G`, the odd antihole inequality
on `H.vertexFinset` is valid for `N₊(FRAC(G))`. -/
theorem exercise_10_15_odd_antihole_inequality_valid_on_nplus_frac_relaxation
    [Fintype V]
    (H : AntiholeSupport V)
    (hH : H.IsContainedIn G)
    (hodd : Odd H.length) :
    is_valid_inequality
      (lovasz_schrijver_nplus_frac_relaxation G)
      (stableSetIndicator H.vertexFinset)
      2 := by
  rw [is_valid_inequality_iff]
  intro x hx
  rw [stableSetIndicator_dotProduct]
  rw [mem_lovasz_schrijver_nplus_frac_relaxation_iff] at hx
  rcases hx with ⟨Y, hYpsd, hTop, hDiag, hColumn, -, hxFirst⟩
  let S : ℝ := H.vertexFinset.sum x
  let T : ℝ :=
    H.vertexFinset.sum (fun j ↦
      H.vertexFinset.sum (fun i ↦ Y (some i) (some j)))
  have hSymm : Y.IsSymm := by
    simpa using hYpsd.isHermitian
  have hEntrySymm (v : V) : Y none (some v) = Y (some v) none := by
    simpa [Matrix.transpose_apply] using
      congr_fun (congr_fun hSymm (some v)) none
  have hSumFirst :
      S = H.vertexFinset.sum (fun v ↦ Y (some v) none) := by
    -- Replace every coordinate of `x` by the first column of its witness.
    dsimp [S]
    apply Finset.sum_congr rfl
    intro v hv
    exact hxFirst v
  have hSNonneg : 0 ≤ S := by
    -- The first-column sum is a sum of nonnegative diagonal entries.
    rw [hSumFirst]
    apply Finset.sum_nonneg
    intro v hv
    rw [hDiag (some v)]
    exact hYpsd.diag_nonneg
  have hColumnBound (v : V) (hv : v ∈ H.vertexFinset) :
      H.vertexFinset.sum (fun i ↦ Y (some i) (some v)) ≤
        2 * Y (some v) none := by
    rcases (AntiholeSupport.mem_vertexFinset_iff H).1 hv with ⟨j, rfl⟩
    have hcenter :
        Y (some (H.verts j)) (some (H.verts j)) = Y none (some (H.verts j)) := by
      calc
        Y (some (H.verts j)) (some (H.verts j)) =
            Y (some (H.verts j)) none := (hDiag _).symm
        _ = Y none (some (H.verts j)) := (hEntrySymm _).symm
    have hbound := fractionalStableSetCone_antiholeSum_le_two_mul_top
      (G := G) H hH j (fun i ↦ Y i (some (H.verts j)))
      (hColumn (H.verts j)) hcenter
    simpa [hEntrySymm] using hbound
  have hSquareBound : S ^ 2 ≤ T := by
    -- The selected PSD principal block controls the square of the first-column sum.
    dsimp [T]
    rw [hSumFirst]
    exact sum_firstColumn_sq_le_principalSum_of_posSemidef
      H.vertexFinset Y hYpsd hTop
  have hPrincipalBound : T ≤ 2 * S := by
    -- Sum the cone-column estimate over all antihole vertices.
    dsimp [T]
    calc
      H.vertexFinset.sum (fun j ↦
          H.vertexFinset.sum (fun i ↦ Y (some i) (some j))) ≤
          H.vertexFinset.sum (fun j ↦ 2 * Y (some j) none) := by
            exact Finset.sum_le_sum fun j hj ↦ hColumnBound j hj
      _ = 2 * H.vertexFinset.sum (fun j ↦ Y (some j) none) := by
        rw [Finset.mul_sum]
      _ = 2 * S := by rw [← hSumFirst]
  -- Combining `S² ≤ T ≤ 2S` with `S ≥ 0` gives the claimed antihole bound.
  dsimp [S] at hSNonneg hSquareBound hPrincipalBound ⊢
  -- Use the stated oddness hypothesis to record positivity of the support length.
  have hodd_ne_zero : H.length ≠ 0 := by
    intro hzero
    rcases hodd with ⟨k, hk⟩
    omega
  have hodd_pos : 0 < H.length := Nat.pos_of_ne_zero hodd_ne_zero
  have hodd_pos_real : (0 : ℝ) < H.length := by
    exact_mod_cast hodd_pos
  nlinarith [hodd_pos_real]

end Exercise_10_15

#print axioms exercise_10_15_odd_antihole_inequality_valid_on_nplus_frac_relaxation
