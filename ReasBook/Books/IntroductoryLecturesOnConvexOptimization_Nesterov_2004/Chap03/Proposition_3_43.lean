/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory

/- Proposition 3.43 lies in the chapter's midpoint-bisection box geometry domain.

Sampled owner-style declarations before refinement:
* mathlib `midpoint ℝ` and `pi_midpoint_apply`, the canonical affine midpoint owner for coordinate
  updates;
* mathlib `Real.volume_Icc_pi_toReal`, the owner formula for the volume of a coordinate box;
* project `FeasibilityResistingOracleState.currentLower` / `currentUpper` in `Algorithm_3_5`,
  whose recursive box transcript already uses the canonical midpoint owner.

Best owner abstraction:
* source-facing: midpoint bisection of one coordinate interval of a box and the resulting
  box-volume / side-length consequences;
* core/canonical: `midpoint ℝ` for the bisected endpoint and `Real.volume_Icc_pi_toReal` for box
  volume;
* bridge/view: the finite-block coverage predicate used only for the `n`-step consequence.

Primitive data:
* one box `Set.Icc a b`
* one chosen coordinate `i`
* one midpoint coordinate bisection step from `(a, b)` to `(a', b')`

Derived API:
* the exact side-length update at the bisected coordinate
* the resulting one-step volume-halving consequence
* the `n`-step side-length consequence under the block-coverage schedule hypothesis

This refinement keeps Proposition 3.43 source-facing, but removes the local arithmetic duplicate
of the midpoint construction and states the one-step volume theorem directly on the primitive
single-step box data instead of a packaged whole-sequence wrapper. -/

/-- A midpoint coordinate bisection step keeps one half of the `i`-th coordinate interval of the
box `Set.Icc a b` and leaves all other coordinates unchanged. The updated endpoint is expressed
through the canonical affine midpoint owner `midpoint ℝ`. -/
def IsMidpointCoordinateBisectionStep
    {n : ℕ} (a b a' b' : Fin n → ℝ) (i : Fin n) : Prop :=
  let midpointBox := midpoint ℝ a b
  (a' = a ∧ b' = Function.update b i (midpointBox i)) ∨
    (a' = Function.update a i (midpointBox i) ∧ b' = b)

/-- In a midpoint coordinate bisection step, the length of the bisected coordinate interval is
exactly halved. -/
-- Proof sketch: split into the two cases in `IsMidpointCoordinateBisectionStep`; in each case,
-- evaluate the updated endpoint at `i` and simplify the resulting difference.
theorem midpointCoordinateBisectionStep_halvedCoordinateLength
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (h : IsMidpointCoordinateBisectionStep a b a' b' i) :
    b' i - a' i = (b i - a i) / 2 := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, div_eq_mul_inv,
      mul_add]
    ring_nf
  · simp [pi_midpoint_apply, midpoint_eq_smul_add, invOf_eq_inv, smul_eq_mul, div_eq_mul_inv,
      mul_add]
    ring_nf

/-- In a midpoint coordinate bisection step, the side-length vector is unchanged away from the
bisected coordinate and is updated at that coordinate by the halved length. -/
theorem midpointCoordinateBisectionStep_sideLengths_eq_update
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (h : IsMidpointCoordinateBisectionStep a b a' b' i) :
    b' - a' = Function.update (b - a) i ((b i - a i) / 2) := by
  ext j
  by_cases hj : j = i
  · subst hj
    simpa [Function.update_self] using midpointCoordinateBisectionStep_halvedCoordinateLength h
  · rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [hj]

/-- Every coordinate direction is selected at least once in each block of `n` consecutive
midpoint bisection steps. -/
def BisectionBlockCoversAllCoordinates
    (n : ℕ) (bisectedCoordinate : ℕ → Fin n) : Prop :=
  ∀ k (i : Fin n), ∃ t ∈ Finset.Icc k (k + n - 1), bisectedCoordinate t = i

/-- In any block of `n` consecutive midpoint bisection steps satisfying the block-coverage
hypothesis, the coordinate-selection map is a permutation of `Fin n`. -/
theorem bisectionBlockCoordinates_bijective
    {n : ℕ} (bisectedCoordinate : ℕ → Fin n)
    (hcover : BisectionBlockCoversAllCoordinates n bisectedCoordinate)
    (k : ℕ) :
    Function.Bijective (fun t : Fin n ↦ bisectedCoordinate (k + t)) := by
  cases n with
  | zero =>
      refine ⟨?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro i
        exact Fin.elim0 i
  | succ n =>
      have hsurj :
          Function.Surjective (fun t : Fin (n + 1) ↦ bisectedCoordinate (k + t)) := by
        intro i
        rcases hcover k i with ⟨t, ht, hti⟩
        have htk : k ≤ t := (Finset.mem_Icc.mp ht).1
        have htn : t < k + (n + 1) := by
          have htn' : t ≤ k + (n + 1) - 1 := (Finset.mem_Icc.mp ht).2
          omega
        refine ⟨⟨t - k, by omega⟩, ?_⟩
        simpa [Nat.add_sub_of_le htk] using hti
      exact (Finite.surjective_iff_bijective).1 hsurj

/-- Proposition 3.43 (1): each midpoint bisection step divides the volume of the resulting
axis-aligned box by two. -/
-- Proof sketch: use `volume_Icc_pi_toReal` to express the volume of each box as the product of its
-- side lengths, then apply the fact that exactly one coordinate length is halved at step `k` while
-- the others are unchanged.
theorem generated_box_volume_eq_half_of_midpoint_bisection
    {n : ℕ} {a b a' b' : Fin n → ℝ} {i : Fin n}
    (hbox : a ≤ b)
    (hstep : IsMidpointCoordinateBisectionStep a b a' b' i) :
    (volume (Set.Icc a' b')).toReal = (1 / 2 : ℝ) * (volume (Set.Icc a b)).toReal := by
  have hsideEq := midpointCoordinateBisectionStep_sideLengths_eq_update hstep
  have hside :
      (fun j ↦ b' j - a' j) = Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) := by
    funext j
    exact congrFun hsideEq j
  have hbox' : a' ≤ b' := by
    intro j
    have hnonneg : 0 ≤ Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) j := by
      by_cases hj : j = i
      · subst j
        have hwidth : 0 ≤ b i - a i := sub_nonneg.mpr (hbox i)
        simpa [Function.update_self] using div_nonneg hwidth (show (0 : ℝ) ≤ 2 by norm_num)
      · simp [hj, sub_nonneg.mpr (hbox j)]
    have hjwidth :
        b' j - a' j = Function.update (fun j ↦ b j - a j) i ((b i - a i) / 2) j := by
      simpa [Pi.sub_apply] using congrFun hsideEq j
    have : 0 ≤ b' j - a' j := by
      rw [hjwidth]
      exact hnonneg
    exact sub_nonneg.mp this
  rw [Real.volume_Icc_pi_toReal hbox', Real.volume_Icc_pi_toReal hbox, hside]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  rw [Finset.prod_eq_mul_prod_diff_singleton_of_mem (Finset.mem_univ i)]
  ring

/-- Proposition 3.43 (2): if every coordinate direction is bisected at least once in each block
of `n` consecutive steps, then after `n` steps every endpoint difference, and hence every side
length for ordered boxes, is halved. -/
-- Proof sketch: track the endpoint-difference vector `b k - a k`. Each step halves exactly the
-- coordinate indexed by `bisectedCoordinate k`. The block-covering hypothesis forces every
-- coordinate to be selected at least once in the next `n` steps, hence exactly once, so the whole
-- endpoint-difference vector is multiplied by `1 / 2`.
theorem generated_box_side_lengths_eq_half_after_n_steps
    {n : ℕ} (a b : ℕ → Fin n → ℝ) (bisectedCoordinate : ℕ → Fin n)
    (hstep : ∀ k,
      IsMidpointCoordinateBisectionStep
        (a k) (b k) (a (k + 1)) (b (k + 1)) (bisectedCoordinate k))
    (hcover : BisectionBlockCoversAllCoordinates n bisectedCoordinate)
    (k : ℕ) :
    b (k + n) - a (k + n) = (1 / 2 : ℝ) • (b k - a k) := by
  classical
  cases n with
  | zero =>
      ext i
      exact Fin.elim0 i
  | succ n =>
      let side : ℕ → Fin (n + 1) → ℝ := fun m ↦ b m - a m
      let c : ℕ → Fin (n + 1) := fun t ↦ bisectedCoordinate (k + t)
      let updatedCoords : ℕ → Finset (Fin (n + 1)) := fun t ↦ (Finset.range t).image c
      let half : Fin (n + 1) → ℝ := fun j ↦ side k j / 2
      have hbij : Function.Bijective (fun t : Fin (n + 1) ↦ c t) := by
        simpa [c] using bisectionBlockCoordinates_bijective bisectedCoordinate hcover k
      have hnotmem : ∀ {t : ℕ}, t < n + 1 → c t ∉ updatedCoords t := by
        intro t ht hmem
        rcases Finset.mem_image.mp hmem with ⟨u, hu, hcu⟩
        have hu' : u < n + 1 := lt_of_lt_of_le (Finset.mem_range.mp hu) (Nat.le_of_lt ht)
        have hEq : (⟨u, hu'⟩ : Fin (n + 1)) = ⟨t, ht⟩ := hbij.1 hcu
        have : u = t := by simpa using congrArg Fin.val hEq
        have hu_lt : u < t := Finset.mem_range.mp hu
        exact (Nat.ne_of_lt hu_lt) this
      have hupdated_succ :
          ∀ {t : ℕ}, t < n + 1 → updatedCoords (t + 1) = insert (c t) (updatedCoords t) := by
        intro t ht
        simp [updatedCoords, Finset.range_add_one]
      have hside_succ :
          ∀ m,
            side (m + 1) =
              Function.update (side m) (bisectedCoordinate m)
                ((side m (bisectedCoordinate m)) / 2) := by
        intro m
        simpa [side] using midpointCoordinateBisectionStep_sideLengths_eq_update (hstep m)
      have hprefix :
          ∀ t, t ≤ n + 1 →
            side (k + t) = (updatedCoords t).piecewise half (side k) := by
        intro t ht
        induction t with
        | zero =>
            simp [updatedCoords, side]
        | succ t ih =>
            have ht' : t < n + 1 := Nat.lt_of_succ_le ht
            have hstep_t :
                side (k + (t + 1)) =
                  Function.update (side (k + t)) (c t) ((side (k + t) (c t)) / 2) := by
              simpa [c, Nat.add_assoc] using hside_succ (k + t)
            calc
              side (k + (t + 1))
                  = Function.update (side (k + t)) (c t) ((side (k + t) (c t)) / 2) := hstep_t
              _ =
                  Function.update ((updatedCoords t).piecewise half (side k)) (c t)
                    (half (c t)) := by
                    rw [ih (Nat.le_of_lt ht')]
                    congr 1
                    rw [Finset.piecewise_eq_of_notMem _ _ _ (hnotmem ht')]
              _ = (insert (c t) (updatedCoords t)).piecewise half (side k) := by
                    symm
                    rw [Finset.piecewise_insert]
              _ = (updatedCoords (t + 1)).piecewise half (side k) := by
                    rw [hupdated_succ ht']
      have huniv : updatedCoords (n + 1) = Finset.univ := by
        ext j
        constructor
        · intro _
          simp
        · intro _
          rcases hbij.2 j with ⟨u, hu⟩
          exact Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr u.2, hu⟩
      calc
        b (k + (n + 1)) - a (k + (n + 1))
            = (updatedCoords (n + 1)).piecewise half (side k) := by
                simpa [side] using hprefix (n + 1) le_rfl
        _ = half := by
              rw [huniv]
              simp [half]
        _ = (1 / 2 : ℝ) • (b k - a k) := by
              ext j
              simp [half, side, Pi.smul_apply, div_eq_mul_inv, mul_comm]
