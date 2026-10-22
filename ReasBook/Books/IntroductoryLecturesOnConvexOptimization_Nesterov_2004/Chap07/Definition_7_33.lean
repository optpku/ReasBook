/-
Authors: Chenyi Li, Siyuan Shao, Yijie Wang, Feiming Wang, Weiran Shi, Yuhao Jiang, Zebo Liu, Wentao Long
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/IntroductoryLecturesOnConvexOptimization_Nesterov_2004/README.md (Contributors).
-/

import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Compat
import IntroductoryLecturesOnConvexOptimization_Nesterov_2004.Chap01.Definition_1_10_2

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section
open scoped Pointwise

variable {ι : Type*}

/- Definition 7.33 lies in the sign-symmetric convex-set domain, with finiteness used only for the
convex-box characterization.

Sampled owner-style declarations:
* `EuclideanSpace.nonnegativeOrthant` and `EuclideanSpace.mem_nonnegativeOrthant_iff` from
  `Chap01/Definition_1_10_2`, the chapter owner for the orthant `ℝⁿ_+`;
* `zeroOneBox` in `Chap01/Definition_1_3_1`, the nearby project owner pattern for intrinsic
  coordinatewise boxes;
* `Pi.abs_apply`, the canonical pointwise absolute-value surface on `ι → ℝ`;
* `Pi.smul_apply`, the canonical pointwise scalar action of `ι → ℝ` on `EuclideanSpace ℝ ι`;
* the later Chapter 7 duplicate local copies in `Theorem_7_8` and `Definition_7_70`, which should
  reuse the owners introduced here rather than re-own them.

Best owner abstraction:
* source-facing: `signVectorSet`, `symmetricBox`, and `IsSignInvariant`;
* core/canonical: the ambient pointwise absolute value on `ι → ℝ`, the pointwise scalar action of
  `ι → ℝ` on `EuclideanSpace ℝ ι`, together with the chapter orthant owner `nonnegativeOrthant`
  after the textbook specialization `ι = Fin n`;
* bridge/view: the coordinatewise membership lemmas and the convex-set characterization by
  symmetric boxes.

Primitive data:
* the coordinate type `ι`;
* a coordinatewise radius function `g : ι → ℝ` for the textbook box `B(g)`;
* a subset `C : Set (EuclideanSpace ℝ ι)`.

Derived API:
* the coordinatewise membership criteria for the sign vectors and symmetric boxes;
* the closure lemma for sign-invariant sets;
* the convex equivalence with symmetric-box containment for the coordinatewise absolute values of
  points of the set.

This refinement keeps the source-facing owners introduced by Definition 7.33, but reowns the
textbook box `B(g)` by the intrinsic coordinatewise interval condition on `EuclideanSpace ℝ ι`
rather than through the implementation transport `ofLp`/`Set.pi`. The public theorem surface can
therefore use the canonical pointwise forms `σ • g` and `B(fun i ↦ |g i|)` directly. The textbook
`ℝⁿ` case is recovered by taking `ι = Fin n`. It leaves the box owner itself in this file so later
Chapter 7 files can reuse it directly instead of re-defining the same set under parallel names.
-/

/-- The sign vectors on a coordinate type `ι`, namely the functions whose coordinates are all
equal to `-1` or `1`. -/
abbrev signVectorSet (ι : Type*) : Set (ι → ℝ) :=
  Set.pi Set.univ fun _ ↦ ({(-1 : ℝ), 1} : Set ℝ)

/-- Membership in `signVectorSet ι` means that every coordinate is a sign. -/
@[simp]
theorem mem_signVectorSet_iff {σ : ι → ℝ} :
    σ ∈ signVectorSet ι ↔ ∀ i, σ i = -1 ∨ σ i = 1 :=
  by simp [signVectorSet]

local notation "E" => EuclideanSpace ℝ ι

/-- The symmetric box `B(g) = {s | -g ≤ s ≤ g}`. -/
abbrev symmetricBox (g : ι → ℝ) : Set E :=
  {s | ∀ i, s i ∈ Set.Icc (-g i) (g i)}

namespace SymmetricBox

/- Source-facing Lean notation for the textbook box `B(g)`. -/
scoped notation:max "B(" g:arg ")" => symmetricBox g

end SymmetricBox

open scoped SymmetricBox

/-- Membership in `symmetricBox g` is the coordinatewise inequality `-g ≤ s ≤ g`. -/
@[simp]
theorem mem_symmetricBox_iff {g : ι → ℝ} {s : E} :
    s ∈ B(g) ↔ ∀ i, -g i ≤ s i ∧ s i ≤ g i :=
  by
    simp [symmetricBox, Set.mem_Icc]

/-- Membership in the symmetric box `B(g)` means that every coordinate of `s` is bounded in
absolute value by the corresponding coordinate of `g`. -/
theorem mem_symmetricBox_iff_abs_le {g : ι → ℝ} {s : E} :
    s ∈ B(g) ↔ ∀ i, |s i| ≤ g i := by
  rw [mem_symmetricBox_iff]
  simp [abs_le]

/-- The sign-invariant sets of Definition 7.33 are the coordinate sets closed under arbitrary
coordinatewise sign changes by sign vectors. -/
def IsSignInvariant (C : Set E) : Prop :=
  ∀ g ∈ C, ∀ σ : ι → ℝ, σ ∈ signVectorSet ι → (σ • g : E) ∈ C

namespace IsSignInvariant

/-- A sign-invariant set contains every coordinatewise sign change of each of its points. -/
theorem smul_mem {C : Set E} (hC : IsSignInvariant C)
    {g : E} {σ : ι → ℝ} (hg : g ∈ C) (hσ : σ ∈ signVectorSet ι) :
    (σ • g : E) ∈ C :=
  hC g hg σ hσ

end IsSignInvariant

/-- Helper for Definition 7.33: replace the `i`-th coordinate of a Euclidean vector by `t`. -/
def coordinateUpdate [DecidableEq ι] (x : E) (i : ι) (t : ℝ) : E :=
  WithLp.toLp 2 (Function.update x i t)

/-- Helper for Definition 7.33: the updated vector has the expected coordinates. -/
@[simp]
lemma coordinateUpdate_apply [DecidableEq ι] (x : E) (i j : ι) (t : ℝ) :
    coordinateUpdate x i t j = if j = i then t else x j := by
  by_cases hji : j = i
  · simp [coordinateUpdate, Function.update, hji]
  · simp [coordinateUpdate, Function.update, hji]

/-- Helper for Definition 7.33: updating a coordinate by its original value does nothing. -/
@[simp]
lemma coordinateUpdate_self [DecidableEq ι] (x : E) (i : ι) :
    coordinateUpdate x i (x i) = x := by
  ext j
  by_cases hji : j = i
  · simp [coordinateUpdate, hji]
  · simp [coordinateUpdate]

/-- Helper for Definition 7.33: coordinatewise multiplication by a sign vector preserves absolute
values. -/
lemma abs_signVector_smul_eq {σ : ι → ℝ} (hσ : σ ∈ signVectorSet ι) (x : E) :
    (fun i ↦ |(σ • x : E) i|) = fun i ↦ |x i| := by
  -- Each coordinate multiplier is `-1` or `1`, so taking absolute values removes it.
  ext i
  rcases (mem_signVectorSet_iff.mp hσ i) with hσi | hσi
  · simp [hσi]
  · simp [hσi]

/-- Helper for Definition 7.33: a sign-invariant set stays closed under flipping one chosen
coordinate. -/
lemma singleCoordinateFlip_mem [DecidableEq ι] {C : Set E} (hC : IsSignInvariant C) {x : E}
    (hx : x ∈ C) (i : ι) : coordinateUpdate x i (-x i) ∈ C := by
  classical
  let σ : ι → ℝ := fun j ↦ if j = i then -1 else 1
  -- The chosen multiplier changes only coordinate `i`, so it is a legitimate sign vector.
  have hσ : σ ∈ signVectorSet ι := by
    rw [mem_signVectorSet_iff]
    intro j
    by_cases hji : j = i
    · left
      simp [σ, hji]
    · right
      simp [σ, hji]
  -- Now rewrite the sign action as the corresponding coordinate update.
  have hσx : (σ • x : E) ∈ C := hC.smul_mem hx hσ
  have hEq : (σ • x : E) = coordinateUpdate x i (-x i) := by
    ext k
    by_cases hki : k = i
    · simp [σ, coordinateUpdate, Function.update, hki]
    · simp [σ, coordinateUpdate, Function.update, hki]
  rw [hEq] at hσx
  exact hσx

/-- Helper for Definition 7.33: from a nonnegative point of a convex sign-invariant set, one may
shrink one coordinate independently and stay inside the set. -/
lemma coordinateUpdate_mem_of_mem_of_nonneg [DecidableEq ι] {C : Set E} (hC_convex : Convex ℝ C)
    (hC : IsSignInvariant C) {x : E} (hx : x ∈ C) (hx_nonneg : ∀ j, 0 ≤ x j) {i : ι} {t : ℝ}
    (ht : 0 ≤ t ∧ t ≤ x i) : coordinateUpdate x i t ∈ C := by
  have hflip : coordinateUpdate x i (-x i) ∈ C := singleCoordinateFlip_mem hC hx i
  by_cases hxi : x i = 0
  · have ht_zero : t = 0 := by linarith [ht.2, hxi]
    have hEq : coordinateUpdate x i t = x := by
      simpa [ht_zero, hxi] using (coordinateUpdate_self x i)
    rw [hEq]
    exact hx
  · have hxi_pos : 0 < x i := lt_of_le_of_ne (hx_nonneg i) (by
      intro h
      exact hxi h.symm)
    let a : ℝ := (x i - t) / (2 * x i)
    let b : ℝ := (x i + t) / (2 * x i)
    have hdenom : (2 * x i) ≠ 0 := by nlinarith
    have ha : 0 ≤ a := by
      dsimp [a]
      exact div_nonneg (sub_nonneg.mpr ht.2) (by positivity)
    have hb : 0 ≤ b := by
      dsimp [b]
      exact div_nonneg (add_nonneg (le_of_lt hxi_pos) ht.1) (by positivity)
    have hab : a + b = 1 := by
      dsimp [a, b]
      field_simp [hdenom]
      ring
    have hcombo :
        a • coordinateUpdate x i (-x i) + b • x = coordinateUpdate x i t := by
      ext j
      by_cases hji : j = i
      · subst hji
        simp [a, b, coordinateUpdate]
        field_simp [hdenom]
        ring
      · calc
          (a • coordinateUpdate x i (-x i) + b • x) j = a * x j + b * x j := by
            simp [coordinateUpdate, hji]
          _ = (a + b) * x j := by ring
          _ = x j := by rw [hab, one_mul]
          _ = (coordinateUpdate x i t) j := by simp [coordinateUpdate, hji]
    -- Express the target update as a convex combination of the flipped vector and `x`.
    have hmem : a • coordinateUpdate x i (-x i) + b • x ∈ C := hC_convex hflip hx ha hb hab
    rw [hcombo] at hmem
    exact hmem

/-- Helper for Definition 7.33: every point in the nonnegative box under `x` belongs to a convex
sign-invariant set once `x` itself does. -/
lemma nonnegativeBox_subset {C : Set E} (hC_convex : Convex ℝ C) (hC : IsSignInvariant C)
    [Finite ι] {x : E} (hx : x ∈ C) (hx_nonneg : ∀ i, 0 ≤ x i) :
    {t : E | ∀ i, 0 ≤ t i ∧ t i ≤ x i} ⊆ C := by
  classical
  letI : Fintype ι := Fintype.ofFinite ι
  intro t ht
  let patched : Finset ι → E := fun S ↦ WithLp.toLp 2 (fun j ↦ if j ∈ S then t j else x j)
  let P : Finset ι → Prop := fun S ↦ patched S ∈ C
  -- Update the coordinates in `S` one at a time, preserving membership in `C`.
  have hP : ∀ S : Finset ι, P S := by
    intro S
    refine Finset.induction_on S ?_ ?_
    · simpa [P, patched] using hx
    · intro i S hiS hS
      let y : E := patched S
      have hy : y ∈ C := by
        simpa [P, y] using hS
      have hy_nonneg : ∀ j, 0 ≤ y j := by
        intro j
        by_cases hjS : j ∈ S
        · simp [y, patched, hjS, (ht j).1]
        · simp [y, patched, hjS, hx_nonneg j]
      have hti : 0 ≤ t i ∧ t i ≤ y i := by
        have hyi : y i = x i := by
          simp [y, patched, hiS]
        refine ⟨(ht i).1, hyi ▸ (ht i).2⟩
      have hupdate : coordinateUpdate y i (t i) ∈ C :=
        coordinateUpdate_mem_of_mem_of_nonneg hC_convex hC hy hy_nonneg hti
      -- Rewriting `update` identifies the new state with the coordinate set `insert i S`.
      have hpatched_insert : coordinateUpdate y i (t i) = patched (insert i S) := by
        ext j
        by_cases hji : j = i
        · subst hji
          simp [y, patched, coordinateUpdate, hiS]
        · by_cases hjS : j ∈ S
          · simp [y, patched, coordinateUpdate, hji, hjS]
          · simp [y, patched, coordinateUpdate, hji, hjS]
      rw [hpatched_insert] at hupdate
      exact hupdate
  -- Once all coordinates are updated, the state is exactly `t`.
  have hpatched_univ : patched Finset.univ = t := by
    ext i
    simp [patched]
  rw [← hpatched_univ]
  exact hP Finset.univ

/-- Definition 7.33: if `C` is convex, sign-invariance is equivalent to containing the full
symmetric box `B(fun i ↦ |g i|)` for every point `g` of `C`. -/
-- Proof sketch: for the forward direction, each sign flip of `g` lies in `C`, so convexity keeps
-- the whole box `B(fun i ↦ |g i|)` inside `C` because its vertices are exactly those sign flips.
-- Conversely, every sign flip `σ ⊙ g` belongs to `B(fun i ↦ |g i|)`, so the assumed box
-- inclusion recovers sign-invariance.
theorem isSignInvariant_iff_symmetricBox_subset_of_convex
    [Finite ι] {C : Set E} (hC_convex : Convex ℝ C) :
    IsSignInvariant C ↔
      ∀ g ∈ C,
        B(fun i ↦ |g i|) ⊆ C := by
  constructor
  · intro hC g hg s hs
    classical
    let σg : ι → ℝ := fun i ↦ if 0 ≤ g i then 1 else -1
    have hσg : σg ∈ signVectorSet ι := by
      rw [mem_signVectorSet_iff]
      intro i
      by_cases hgi : 0 ≤ g i
      · right
        simp [σg, hgi]
      · left
        simp [σg, hgi]
    -- First move from `g` to the nonnegative point `|g|`.
    have hσg_mem : (σg • g : E) ∈ C := hC.smul_mem hg hσg
    let gAbs : E := WithLp.toLp 2 (fun i ↦ |g i|)
    have habsg : gAbs ∈ C := by
      have hσg_abs : (σg • g : E) = gAbs := by
        ext i
        by_cases hgi : 0 ≤ g i
        · simp [σg, gAbs, hgi, abs_of_nonneg hgi]
        · have hgi' : g i < 0 := lt_of_not_ge hgi
          simp [σg, gAbs, hgi, abs_of_neg hgi']
      rw [hσg_abs] at hσg_mem
      exact hσg_mem
    let sAbs : E := WithLp.toLp 2 (fun i ↦ |s i|)
    have habss : sAbs ∈ C := by
      -- The nonnegative box below `|g|` lies in `C`, so it contains `|s|`.
      refine nonnegativeBox_subset hC_convex hC habsg (fun i ↦ by simp [gAbs]) ?_
      intro i
      simpa [sAbs, gAbs] using
        (show 0 ≤ |s i| ∧ |s i| ≤ |g i| from ⟨abs_nonneg _, (mem_symmetricBox_iff_abs_le.mp hs i)⟩)
    let τs : ι → ℝ := fun i ↦ if 0 ≤ s i then 1 else -1
    have hτs : τs ∈ signVectorSet ι := by
      rw [mem_signVectorSet_iff]
      intro i
      by_cases hsi : 0 ≤ s i
      · right
        simp [τs, hsi]
      · left
        simp [τs, hsi]
    -- Then restore the original signs of `s` from its absolute-value vector.
    have hτs_abs : (τs • sAbs : E) = s := by
      ext i
      by_cases hsi : 0 ≤ s i
      · simp [τs, sAbs, hsi, abs_of_nonneg hsi]
      · have hsi' : s i < 0 := lt_of_not_ge hsi
        simp [τs, sAbs, hsi, abs_of_neg hsi']
    have hs_mem : (τs • sAbs : E) ∈ C := hC.smul_mem habss hτs
    rw [hτs_abs] at hs_mem
    exact hs_mem
  · intro hbox g hg σ hσ
    -- Any sign change of `g` remains inside the symmetric box centered at the origin with radius
    -- `|g|`, so the assumed box containment gives the result.
    have hbox_mem : (σ • g : E) ∈ B(fun i ↦ |g i|) := by
      rw [mem_symmetricBox_iff_abs_le]
      intro i
      rcases mem_signVectorSet_iff.mp hσ i with hσi | hσi
      · simp [hσi]
      · simp [hσi]
    exact hbox g hg hbox_mem
