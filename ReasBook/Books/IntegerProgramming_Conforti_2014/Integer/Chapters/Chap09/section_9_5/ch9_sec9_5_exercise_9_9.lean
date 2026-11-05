/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_1.ch9_sec9_1_2_theorem_9_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_definition_5_1_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap09.section_9_5.ch9_sec9_5_exercise_9_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap05.section_5_1.ch5_sec5_1_remark_5_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_1_theorem_1_8
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap01.section_1_5.ch1_sec1_5_2_lemma_1_3
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Topology.MetricSpace.Thickening

-- Declarations for this item will be appended below by the statement pipeline.

-- This exercise reuses the Chapter 9 flatness-theorem owners for embedded integral points and
-- integral directions.

open scoped DirectionalWidthNotation IntegerVectorNotation Matrix Pointwise

section Exercise99

variable {n : ℕ}

/-- Helper for Exercise 9.9: `SplitCoverProperty n c` means that every lattice-free convex body in
`ℝ^n` is covered by `c` open split strips. Full dimensionality is deliberately absent so the
property can be applied to affine slices in the dimension induction. -/
abbrev SplitCoverProperty (n c : ℕ) : Prop :=
  ∀ K : ConvexBody (Fin n → ℝ),
    ¬ K.ContainsIntegralPoint →
    ∃ π : Fin c → {π : Fin n → ℤ // π ≠ 0},
      ∃ π₀ : Fin c → ℤ,
        (K : Set (Fin n → ℝ)) ⊆
          ⋃ i : Fin c, split_strip (π i).1 (π₀ i)

/-- Helper for Exercise 9.9: in dimension `0`, every convex body already contains the unique
integral point. -/
lemma contains_integral_point_fin_zero
    (K : ConvexBody (Fin 0 → ℝ)) :
    K.ContainsIntegralPoint := by
  -- Any point of `K` is the unique point of `ℝ^0`, hence it is integral.
  change _root_.contains_integral_point (K : Set (Fin 0 → ℝ))
  rcases K.nonempty with ⟨x, hx⟩
  refine ⟨x, hx, ?_⟩
  rw [mem_integerVectors_iff]
  refine ⟨fun i ↦ Fin.elim0 i, ?_⟩
  funext i
  exact Fin.elim0 i

/-- Helper for Exercise 9.9: the zero-dimensional cover statement is vacuous because the
lattice-free hypothesis is impossible. -/
lemma split_cover_property_zero_dimensional :
    SplitCoverProperty 0 0 := by
  intro K hfree
  -- The lattice-free assumption contradicts the unique integral point in `ℝ^0`.
  exfalso
  exact hfree (contains_integral_point_fin_zero K)

/-- Helper for Exercise 9.9: in `ℝ`, a point whose unique coordinate is an integer is already an
integral point of the ambient convex body. -/
lemma contains_integral_point_of_eq_int_one_dimensional
    (K : ConvexBody (Fin 1 → ℝ))
    {x : Fin 1 → ℝ}
    (hx : x ∈ K)
    {m : ℤ}
    (hm : x 0 = (m : ℝ)) :
    K.ContainsIntegralPoint := by
  -- Rewrite `x` as the real embedding of the constant integer vector.
  change _root_.contains_integral_point (K : Set (Fin 1 → ℝ))
  apply (contains_integral_point_iff).2
  refine ⟨fun _ ↦ m, ?_⟩
  have hx_eq : (Int.cast ∘ fun _ : Fin 1 ↦ m) = x := by
    funext i
    fin_cases i
    simpa [Function.comp] using hm.symm
  simpa [hx_eq] using hx

/-- Helper for Exercise 9.9: if a one-dimensional convex body meets both sides of an integer level,
then convexity forces it to contain that integral point. -/
lemma contains_integral_point_of_between_one_dimensional
    (K : ConvexBody (Fin 1 → ℝ))
    {x y : Fin 1 → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K)
    {m : ℤ}
    (hleft : x 0 ≤ (m : ℝ))
    (hright : (m : ℝ) ≤ y 0) :
    K.ContainsIntegralPoint := by
  by_cases hxy : x 0 = y 0
  · -- If the endpoints agree, the common coordinate is already the desired integer.
    have hm : x 0 = (m : ℝ) := by
      apply le_antisymm hleft
      simpa [hxy] using hright
    exact contains_integral_point_of_eq_int_one_dimensional K hx hm
  · -- Otherwise interpolate to the unique point whose coordinate equals `m`.
    have hlt : x 0 < y 0 := lt_of_le_of_ne (le_trans hleft hright) hxy
    let t : ℝ := ((m : ℝ) - x 0) / (y 0 - x 0)
    have hden : y 0 - x 0 ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
    have ht0 : 0 ≤ t := by
      dsimp [t]
      refine div_nonneg ?_ ?_
      · linarith
      · linarith
    have ht1 : t ≤ 1 := by
      have hnum_le : (m : ℝ) - x 0 ≤ y 0 - x 0 := by
        linarith
      have hden_nonneg : 0 ≤ y 0 - x 0 := by
        linarith
      have hdiv :
          ((m : ℝ) - x 0) / (y 0 - x 0) ≤ (y 0 - x 0) / (y 0 - x 0) :=
        div_le_div_of_nonneg_right hnum_le hden_nonneg
      simpa [t, hden] using hdiv
    let z : Fin 1 → ℝ := (1 - t) • x + t • y
    have hz_mem : z ∈ K := by
      -- Convexity keeps the interpolated point inside the convex body.
      simpa [z] using
        (convex_iff_add_mem.mp K.convex) hx hy
          (a := 1 - t) (b := t)
          (by linarith) ht0 (by ring)
    have hmul : t * (y 0 - x 0) = (m : ℝ) - x 0 := by
      dsimp [t]
      field_simp [hden]
    have hz_eq : z 0 = (m : ℝ) := by
      calc
        z 0 = (1 - t) * x 0 + t * y 0 := by
          simp [z]
        _ = x 0 + t * (y 0 - x 0) := by ring
        _ = (m : ℝ) := by linarith
    exact contains_integral_point_of_eq_int_one_dimensional K hz_mem hz_eq

/-- Helper for Exercise 9.9: every one-dimensional full-dimensional lattice-free convex body lies in
a single open split strip. -/
lemma exists_single_open_split_cover_one_dimensional :
    SplitCoverProperty 1 1 := by
  intro K hfree
  rcases K.nonempty with ⟨x₀, hx₀⟩
  let πvec : Fin 1 → ℤ := fun _ ↦ 1
  have hπvec_nonzero : πvec ≠ 0 := by
    intro hπ
    have hzero : πvec 0 = 0 := by
      simpa using congrFun hπ 0
    norm_num [πvec] at hzero
  let π : Fin 1 → {π : Fin 1 → ℤ // π ≠ 0} := fun _ ↦ ⟨πvec, hπvec_nonzero⟩
  let π₀ : Fin 1 → ℤ := fun _ ↦ Int.floor (x₀ 0)
  refine ⟨π, π₀, ?_⟩
  intro y hy
  have hy_lower : (Int.floor (x₀ 0) : ℝ) < y 0 := by
    by_contra hy_not
    have hy_le : y 0 ≤ (Int.floor (x₀ 0) : ℝ) := not_lt.mp hy_not
    have hbad :=
      contains_integral_point_of_between_one_dimensional
        K hy hx₀ hy_le (Int.floor_le (x₀ 0))
    exact hfree hbad
  have hy_upper : y 0 < (Int.floor (x₀ 0) : ℝ) + 1 := by
    by_contra hy_not
    have hy_ge : (Int.floor (x₀ 0) : ℝ) + 1 ≤ y 0 := not_lt.mp hy_not
    have hx₀_le_next : x₀ 0 ≤ ((Int.floor (x₀ 0) + 1 : ℤ) : ℝ) := by
      -- Cast the standard `floor < a + 1` estimate to the integer level used by the helper.
      simpa [Int.cast_add] using le_of_lt (Int.lt_floor_add_one (x₀ 0))
    have hbad :=
      contains_integral_point_of_between_one_dimensional
        K hx₀ hy (m := Int.floor (x₀ 0) + 1)
        hx₀_le_next (by simpa using hy_ge)
    exact hfree hbad
  have hy_strip : y ∈ split_strip (π 0).1 (π₀ 0) := by
    -- In dimension one, the split scalar product is just the unique coordinate.
    have hsplit_dot : split_dot (π 0).1 y = y 0 := by
      rw [split_dot_eq_sum]
      simp [π, πvec]
    rw [mem_split_strip_iff, hsplit_dot]
    exact And.intro hy_lower hy_upper
  exact Set.mem_iUnion.2 ⟨0, hy_strip⟩

/-- Helper for Exercise 9.9: flatness plus width attainment produces a nonzero integral direction
whose width `w_{d}(K)` is bounded purely in terms of the ambient dimension. -/
lemma exists_bounded_flat_direction
    {n : ℕ}
    (hn : 0 < n)
    {k : ℕ → ℝ}
    (hk : ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
      K.FullDimensional →
      ¬ K.ContainsIntegralPoint →
      lattice_width K ≤ k n)
    (K : ConvexBody (Fin n → ℝ))
    (hfree : ¬ K.ContainsIntegralPoint) :
    ∃ d : {d : Fin n → ℤ // d ≠ 0},
      w_{d.1}(K) ≤ k n := by
  -- The compact lattice and its closed complement are disjoint. Thicken `K` slightly while
  -- staying away from the lattice, which supplies the full dimensionality needed by flatness.
  have hintegerClosed : IsClosed (integerVectors n : Set (Fin n → ℝ)) := by
    rw [show (integerVectors n : Set (Fin n → ℝ)) =
        ⋂ i : Fin n, (fun x : Fin n → ℝ ↦ x i) ⁻¹' Set.range (Int.cast : ℤ → ℝ) by
      ext x
      simp [mem_integerVectors_iff_forall]]
    exact isClosed_iInter fun i ↦
      Int.isClosedEmbedding_coe_real.isClosed_range.preimage (continuous_apply i)
  have hKsub : (K : Set (Fin n → ℝ)) ⊆ (integerVectors n : Set (Fin n → ℝ))ᶜ := by
    intro x hxK hxZ
    exact hfree (contains_integral_point_iff.2
      ((mem_integerVectors_iff.mp hxZ).imp fun z hz ↦ by simpa [hz] using hxK))
  rcases K.isCompact.exists_cthickening_subset_open hintegerClosed.isOpen_compl hKsub with
    ⟨δ, hδ, hδK⟩
  let T : ConvexBody (Fin n → ℝ) :=
    ⟨Metric.cthickening δ (K : Set (Fin n → ℝ)),
      K.convex.cthickening δ,
      K.isCompact.cthickening,
      K.nonempty.mono (fun x hx ↦ Metric.self_subset_cthickening (K : Set (Fin n → ℝ)) hx)⟩
  have hTfull : T.FullDimensional := by
    rcases K.nonempty with ⟨x, hxK⟩
    refine ⟨x, ?_⟩
    exact Metric.thickening_subset_interior_cthickening δ (K : Set (Fin n → ℝ))
      (Metric.self_subset_thickening hδ _ hxK)
  have hTfree : ¬ T.ContainsIntegralPoint := by
    intro hT
    rcases T.containsIntegralPoint_iff.1 hT with ⟨z, hzT⟩
    exact hδK hzT (mem_integerVectors_iff.2 ⟨z, rfl⟩)
  -- Realize the lattice width of the thickening and compare the width back down to `K`.
  obtain ⟨d, hd_ne, hd⟩ :=
    exists_integral_direction_ne_zero_realizing_lattice_width hn T hTfull
  refine ⟨⟨d, hd_ne⟩, ?_⟩
  have hKT : (K : Set (Fin n → ℝ)) ⊆ (T : Set (Fin n → ℝ)) :=
    fun x hx ↦ Metric.self_subset_cthickening (K : Set (Fin n → ℝ)) hx
  have hmono : w_{d}(K) ≤ w_{d}(T) :=
    directionalWidth_mono K.nonempty T.isCompact hKT
  calc
    w_{d}(K) ≤ w_{d}(T) := hmono
    _ = lattice_width T := hd.symm
    _ ≤ k n := hk T hTfull hTfree

/-- Helper for Exercise 9.9: if the gcd of the coordinate absolute values is one, then the
normalized integer coefficient gcd is one. -/
lemma coefficientGcd_eq_one_of_coordinateGcd_eq_one
    (a : Fin n → ℤ)
    (ha : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (a i)) = 1) :
    coefficientGcd a = 1 := by
  have hnatAbsDvd :
      Int.natAbs (coefficientGcd a) ∣
        Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (a i)) := by
    refine Finset.dvd_gcd ?_
    intro i _
    exact Int.natAbs_dvd_natAbs.mpr (coefficientGcd_dvd a i)
  have hnatAbsEqOne : Int.natAbs (coefficientGcd a) = 1 :=
    Nat.dvd_one.mp (by simpa [ha] using hnatAbsDvd)
  have hcoeffNonneg : 0 ≤ coefficientGcd a :=
    Int.nonneg_of_normalize_eq_self (Finset.normalize_gcd (s := Finset.univ) (f := a))
  calc
    coefficientGcd a = (Int.natAbs (coefficientGcd a) : ℤ) := by
      symm
      exact Int.natAbs_of_nonneg hcoeffNonneg
    _ = 1 := by exact_mod_cast hnatAbsEqOne

/-- Helper for Exercise 9.9: normalizing a nonzero integral direction by its positive coefficient
gcd gives a primitive direction whose width is no larger than the original width. -/
lemma exists_primitive_direction_le_width
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ)
    (hd : d ≠ 0) :
    ∃ a : Fin n → ℤ,
      a ≠ 0 ∧
      coefficientGcd a = 1 ∧
      w_{a}(K) ≤ w_{d}(K) := by
  let g : ℕ := Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (d i))
  let a : Fin n → ℤ := fun i ↦ d i / g
  have hg : 0 < g := by
    simpa [g] using coordinate_gcd_pos d hd
  have ha_gcd : Finset.univ.gcd (fun i : Fin n ↦ Int.natAbs (a i)) = 1 := by
    simpa [a, g] using normalized_split_vector_gcd_eq_one d hd
  have ha_coeff : coefficientGcd a = 1 := by
    exact coefficientGcd_eq_one_of_coordinateGcd_eq_one a ha_gcd
  have ha : a ≠ 0 := by
    intro ha0
    rw [ha0] at ha_coeff
    have hzero : coefficientGcd (0 : Fin n → ℤ) = 0 := by
      rw [coefficientGcd, Finset.gcd_eq_zero_iff]
      intro i _
      rfl
    rw [hzero] at ha_coeff
    norm_num at ha_coeff
  have hpoint : ∀ x : Fin n → ℝ, split_dot d x = (g : ℝ) * split_dot a x := by
    intro x
    simpa [a, g] using normalized_split_dot_eq_gcd_mul d hd x
  have himage :
      integral_direction_linear_form d '' (K : Set (Fin n → ℝ)) =
        (fun t : ℝ ↦ (g : ℝ) * t) ''
          (integral_direction_linear_form a '' (K : Set (Fin n → ℝ))) := by
    ext t
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨integral_direction_linear_form a x, ⟨x, hx, rfl⟩, ?_⟩
      simpa [integral_direction_linear_form, split_dot] using (hpoint x).symm
    · rintro ⟨t, ⟨x, hx, rfl⟩, rfl⟩
      refine ⟨x, hx, ?_⟩
      simpa [integral_direction_linear_form, split_dot] using hpoint x
  have hwidth : w_{d}(K) = (g : ℝ) * w_{a}(K) := by
    let S : Set ℝ := integral_direction_linear_form a '' (K : Set (Fin n → ℝ))
    have hsmul : (fun t : ℝ ↦ (g : ℝ) * t) '' S = (g : ℝ) • S := by
      ext t
      constructor
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
      · rintro ⟨u, hu, rfl⟩
        exact ⟨u, hu, rfl⟩
    rw [directional_width, himage]
    change sSup ((fun t : ℝ ↦ (g : ℝ) * t) '' S) -
        sInf ((fun t : ℝ ↦ (g : ℝ) * t) '' S) = _
    rw [hsmul]
    rw [Real.sSup_smul_of_nonneg (by positivity), Real.sInf_smul_of_nonneg (by positivity)]
    simp only [smul_eq_mul, directional_width, S]
    ring
  have hwidth_a_nonneg : 0 ≤ w_{a}(K) := directionalWidth_nonneg K a
  refine ⟨a, ha, ha_coeff, ?_⟩
  calc
    w_{a}(K) ≤ (g : ℝ) * w_{a}(K) := by
      have hg_one : (1 : ℝ) ≤ g := by exact_mod_cast hg
      nlinarith
    _ = w_{d}(K) := hwidth.symm

/-- Helper for Exercise 9.9: a compact convex body whose split width is at most `B` has all of its
attained floor levels in one window of `⌈B⌉ + 1` consecutive integers. -/
lemma exists_floor_window_of_split_dot_bound
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (a : Fin n → ℤ)
    {x₀ : Fin n → ℝ}
    (hx₀ : x₀ ∈ K)
    {B : ℝ}
    (_hB : 0 ≤ B)
    (hwidth : w_{a}(K) ≤ B) :
    ∃ L : ℤ,
      ∀ x ∈ K, ∃ j : Fin (Nat.ceil B + 1),
        Int.floor (split_dot a x) = L + j := by
  let C : ℕ := Nat.ceil B
  let S : Set ℝ := split_dot a '' (K : Set (Fin n → ℝ))
  have hcont : Continuous fun x : Fin n → ℝ ↦ split_dot a x := by
    have hsum : Continuous fun x : Fin n → ℝ ↦ ∑ i : Fin n, (a i : ℝ) * x i := by
      refine continuous_finsetSum _ ?_
      intro i _
      exact continuous_const.mul (continuous_apply i)
    simpa [split_dot_eq_sum] using hsum
  have hcompact : IsCompact S := by
    simpa [S] using K.isCompact.image hcont
  have hne : S.Nonempty := ⟨split_dot a x₀, x₀, hx₀, rfl⟩
  let L : ℤ := Int.floor (sInf S)
  refine ⟨L, ?_⟩
  intro x hx
  have hxS : split_dot a x ∈ S := ⟨x, hx, rfl⟩
  have hx_lower : (L : ℝ) ≤ split_dot a x := by
    exact le_trans (Int.floor_le (sInf S)) (csInf_le hcompact.bddBelow hxS)
  have hx_upper : split_dot a x < ((L + C : ℤ) : ℝ) + 1 := by
    have hle_max : split_dot a x ≤ sSup S := le_csSup hcompact.bddAbove hxS
    have hmax_min : sSup S - sInf S ≤ w_{a}(K) := by
      have himage :
          integral_direction_linear_form a '' (K : Set (Fin n → ℝ)) = S := by
        ext t
        constructor
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, by
            apply congrArg (fun f : Fin n → ℝ => f ⬝ᵥ x)
            funext j
            rfl⟩
        · rintro ⟨x, hx, rfl⟩
          exact ⟨x, hx, by
            apply congrArg (fun f : Fin n → ℝ => f ⬝ᵥ x)
            funext j
            rfl⟩
      rw [directional_width, himage]
    have hle_shift : split_dot a x ≤ sInf S + B := by
      linarith
    have hBC : B ≤ (C : ℝ) := Nat.le_ceil B
    have hlt_shift : split_dot a x < (Int.floor (sInf S) : ℝ) + (C : ℝ) + 1 := by
      have hupper := Int.lt_floor_add_one (sInf S)
      linarith
    simpa [L, add_assoc] using hlt_shift
  have hbetween : L ≤ Int.floor (split_dot a x) := by
    exact Int.le_floor.mpr hx_lower
  have hle : Int.floor (split_dot a x) ≤ L + C := by
    by_contra hnot
    have hge : L + C + 1 ≤ Int.floor (split_dot a x) := by omega
    have hge_real : ((L + C : ℤ) : ℝ) + 1 ≤
        (Int.floor (split_dot a x) : ℝ) := by
      exact_mod_cast hge
    have hfloorle : (Int.floor (split_dot a x) : ℝ) ≤ split_dot a x :=
      Int.floor_le _
    have hbad : ((L + C : ℤ) : ℝ) + 1 ≤ split_dot a x :=
      le_trans hge_real hfloorle
    linarith
  let j : Fin (C + 1) :=
    ⟨Int.toNat (Int.floor (split_dot a x) - L), by
      rw [Int.toNat_lt]
      · omega
      · omega⟩
  refine ⟨j, ?_⟩
  dsimp [j]
  rw [← Int.toNat_of_nonneg (sub_nonneg.mpr hbetween)]
  omega

/-- Helper for Exercise 9.9: the real linear action of an integral square matrix. -/
noncomputable def integerMatrixAction {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℝ) : Fin n → ℝ :=
  (U.map (Int.castRingHom ℝ)) *ᵥ x

/-- Helper for Exercise 9.9: composing integral matrix actions agrees with multiplying the
integral matrices first. -/
lemma integerMatrixAction_mul {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℤ) (x : Fin n → ℝ) :
    integerMatrixAction (V * U) x = integerMatrixAction V (integerMatrixAction U x) := by
  rw [integerMatrixAction, integerMatrixAction, integerMatrixAction]
  rw [Matrix.map_mul]
  rw [Matrix.mulVec_mulVec]

/-- Helper for Exercise 9.9: the identity integral matrix acts as the identity on real vectors. -/
@[simp]
lemma integerMatrixAction_one {n : ℕ} (x : Fin n → ℝ) :
    integerMatrixAction (1 : Matrix (Fin n) (Fin n) ℤ) x = x := by
  simp [integerMatrixAction]

/-- Helper for Exercise 9.9: an integral matrix action with an integral left inverse is
injective. -/
lemma integerMatrixAction_injective {n : ℕ}
    (U V : Matrix (Fin n) (Fin n) ℤ)
    (hVU : V * U = 1) :
    Function.Injective (integerMatrixAction U) := by
  intro x y hxy
  calc
    x = integerMatrixAction (1 : Matrix (Fin n) (Fin n) ℤ) x := by simp
    _ = integerMatrixAction (V * U) x := by rw [hVU]
    _ = integerMatrixAction V (integerMatrixAction U x) :=
      integerMatrixAction_mul U V x
    _ = integerMatrixAction V (integerMatrixAction U y) := by rw [hxy]
    _ = integerMatrixAction (V * U) y :=
      (integerMatrixAction_mul U V y).symm
    _ = y := by
      rw [hVU]
      simp

/-- Helper for Exercise 9.9: a unimodular integral matrix action preserves the integer lattice. -/
lemma integerMatrixAction_mem_integerVectors_iff {n : ℕ}
    (U : Matrix (Fin n) (Fin n) ℤ)
  (hU : IsUnit U.det)
  (x : Fin n → ℝ) :
    integerMatrixAction U x ∈ ℤ^n ↔ x ∈ ℤ^n := by
  exact (Matrix.isUnit_det_iff_mulVec_mem_integerVectors U).mp hU x

/-- Helper for Exercise 9.9: a primitive integral row is the first row of an integral matrix
with an explicit two-sided integral inverse. -/
lemma exists_unimodular_matrix_with_first_row
    {n : ℕ}
    (hn : 0 < n)
    (a : Fin n → ℤ)
    (ha : coefficientGcd a = 1) :
    ∃ U V : Matrix (Fin n) (Fin n) ℤ,
      U * V = 1 ∧ V * U = 1 ∧ IsUnit U.det ∧ U ⟨0, hn⟩ = a := by
  rcases exists_unimodular_normalFormAux a with ⟨T, V, hTV, hVT, hform⟩
  have hsingle : a ᵥ* T = Pi.single ⟨0, hn⟩ (1 : ℤ) := by
    rw [hform]
    ext j
    by_cases hj : j = ⟨0, hn⟩
    · subst hj
      simp [coefficientGcdNormalFormRow, ha]
    · have hj0 : j.1 ≠ 0 := by
        intro hj0
        exact hj (Fin.ext hj0)
      simp [coefficientGcdNormalFormRow, Pi.single, hj, hj0]
  have hrow : V ⟨0, hn⟩ = a := by
    calc
      V ⟨0, hn⟩ = V.row ⟨0, hn⟩ := rfl
      _ = (Pi.single ⟨0, hn⟩ (1 : ℤ) : Fin n → ℤ) ᵥ* V := by
        symm
        exact Matrix.single_one_vecMul ⟨0, hn⟩ V
      _ = (a ᵥ* T) ᵥ* V := by rw [hsingle]
      _ = a ᵥ* (T * V) := by rw [Matrix.vecMul_vecMul]
      _ = a := by simp [hTV]
  have hVdet : IsUnit V.det := Matrix.isUnit_det_of_right_inverse hVT
  exact ⟨V, T, hVT, hTV, hVdet, hrow⟩

/-- Helper for Exercise 9.9: if the first row of an integral matrix is `a`, then the first
coordinate of its real action is the split functional `split_dot a`. -/
lemma integerMatrixAction_zero_eq_split_dot
    {n : ℕ}
    (hn : 0 < n)
    (U : Matrix (Fin n) (Fin n) ℤ)
    (a : Fin n → ℤ)
    (hrow : U ⟨0, hn⟩ = a)
    (x : Fin n → ℝ) :
    integerMatrixAction U x ⟨0, hn⟩ = split_dot a x := by
  simp [integerMatrixAction, Matrix.mulVec, dotProduct, split_dot, hrow]

/-- Helper for Exercise 9.9: the standard first-coordinate integral direction in positive
dimension. -/
def standardIntegralDirection {n : ℕ} (hn : 0 < n) : Fin n → ℤ :=
  Pi.single ⟨0, hn⟩ 1

/-- Helper for Exercise 9.9: the standard first-coordinate integral direction is nonzero. -/
lemma standardIntegralDirection_ne_zero {n : ℕ} (hn : 0 < n) :
    standardIntegralDirection hn ≠ 0 := by
  intro hzero
  have hcoord := congrFun hzero ⟨0, hn⟩
  simp [standardIntegralDirection] at hcoord

/-- Helper for Exercise 9.9: the affine slice of the unimodular image of `K` at integer level
`c`, expressed in the tail coordinates. -/
def integerMatrixAffineSlice {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (c : ℤ) : Set (Fin n → ℝ) :=
  {v | Fin.cons (c : ℝ) v ∈
    integerMatrixAction U '' (K : Set (Fin (n + 1) → ℝ))}

/-- Helper for Exercise 9.9: an affine slice of a convex body under an invertible linear image is
convex. -/
lemma integerMatrixAffineSlice_convex {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (c : ℤ) :
    Convex ℝ (integerMatrixAffineSlice U K c) := by
  intro x hx y hy a b ha hb hab
  rcases hx with ⟨x₀, hx₀, hx_eq⟩
  rcases hy with ⟨y₀, hy₀, hy_eq⟩
  refine ⟨a • x₀ + b • y₀, K.convex hx₀ hy₀ ha hb hab, ?_⟩
  calc
    integerMatrixAction U (a • x₀ + b • y₀) =
        a • integerMatrixAction U x₀ + b • integerMatrixAction U y₀ := by
      simp [integerMatrixAction, Matrix.mulVec_add, Matrix.mulVec_smul]
    _ = a • Fin.cons (c : ℝ) x + b • Fin.cons (c : ℝ) y := by
      rw [hx_eq, hy_eq]
    _ = Fin.cons (c : ℝ) (a • x + b • y) := by
      ext i
      cases i using Fin.cases
      · simp only [Fin.cons_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        calc
          a * (c : ℝ) + b * (c : ℝ) = (a + b) * (c : ℝ) := by ring
          _ = (c : ℝ) := by rw [hab, one_mul]
      · simp

/-- Helper for Exercise 9.9: an affine slice of a compact convex body under an integral matrix
action is compact. -/
lemma integerMatrixAffineSlice_isCompact {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (c : ℤ) :
    IsCompact (integerMatrixAffineSlice U K c) := by
  have hcoord : ∀ i : Fin (n + 1),
      Continuous fun x : Fin (n + 1) → ℝ ↦ integerMatrixAction U x i := by
    intro i
    have hsum : Continuous fun x : Fin (n + 1) → ℝ ↦
        ∑ j : Fin (n + 1), (U i j : ℝ) * x j := by
      refine continuous_finsetSum _ ?_
      intro j _
      exact continuous_const.mul (continuous_apply j)
    simpa [integerMatrixAction, Matrix.mulVec, dotProduct] using hsum
  have haction : Continuous (integerMatrixAction U) := continuous_pi hcoord
  have htail : Continuous fun x : Fin (n + 1) → ℝ ↦
      Fin.tail (integerMatrixAction U x) :=
    continuous_pi fun i ↦ hcoord i.succ
  have hclosed : IsClosed {x : Fin (n + 1) → ℝ |
      integerMatrixAction U x ⟨0, Nat.succ_pos n⟩ = (c : ℝ)} :=
    isClosed_eq (hcoord ⟨0, Nat.succ_pos n⟩) continuous_const
  have hsubCompact : IsCompact
      ((K : Set (Fin (n + 1) → ℝ)) ∩
        {x | integerMatrixAction U x ⟨0, Nat.succ_pos n⟩ = (c : ℝ)}) :=
    K.isCompact.inter_right hclosed
  have himage : integerMatrixAffineSlice U K c =
      (fun x : Fin (n + 1) → ℝ ↦ Fin.tail (integerMatrixAction U x)) ''
        ((K : Set (Fin (n + 1) → ℝ)) ∩
          {x | integerMatrixAction U x ⟨0, Nat.succ_pos n⟩ = (c : ℝ)}) := by
    ext v
    constructor
    · rintro ⟨x, hxK, hx_eq⟩
      refine ⟨x, ⟨hxK, ?_⟩, ?_⟩
      · exact congrFun hx_eq ⟨0, Nat.succ_pos n⟩
      · have htail_eq := congrArg Fin.tail hx_eq
        simpa using htail_eq
    · rintro ⟨x, ⟨hxK, hx0⟩, rfl⟩
      refine ⟨x, hxK, ?_⟩
      have hx0' :
          integerMatrixAction U x ⟨0, Nat.succ_pos n⟩ = (c : ℝ) := hx0
      rw [← Fin.cons_self_tail (integerMatrixAction U x)]
      exact congrArg
        (fun t ↦ Fin.cons t (Fin.tail (integerMatrixAction U x))) hx0'
  rw [himage]
  exact hsubCompact.image htail

/-- Helper for Exercise 9.9: an integer affine slice of a unimodular image preserves
lattice-freeness. -/
lemma integerMatrixAffineSlice_not_containsIntegralPoint {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hU : IsUnit U.det)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (hfree : ¬ K.ContainsIntegralPoint)
    (c : ℤ) :
    ¬ _root_.contains_integral_point (integerMatrixAffineSlice U K c) := by
  rintro ⟨v, hv, hvZ⟩
  rcases hv with ⟨x, hxK, hx_eq⟩
  rcases mem_integerVectors_iff.mp hvZ with ⟨z, hz⟩
  have hyZ : integerMatrixAction U x ∈ integerVectors (n + 1) := by
    rw [hx_eq]
    rw [mem_integerVectors_iff]
    refine ⟨Fin.cons c z, ?_⟩
    ext i
    cases i using Fin.cases <;> simp [hz]
  have hxZ : x ∈ integerVectors (n + 1) :=
    (integerMatrixAction_mem_integerVectors_iff U hU x).mp hyZ
  rcases mem_integerVectors_iff.mp hxZ with ⟨w, hw⟩
  exact hfree (contains_integral_point_iff.2 ⟨w, by simpa [hw] using hxK⟩)

/-- Helper for Exercise 9.9: a nonempty compact affine slice inherits the convex-body
structure. -/
noncomputable def integerMatrixAffineSliceConvexBody {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (c : ℤ)
    (hne : (integerMatrixAffineSlice U K c).Nonempty) :
    ConvexBody (Fin n → ℝ) where
  carrier := integerMatrixAffineSlice U K c
  convex' := integerMatrixAffineSlice_convex U K c
  isCompact' := integerMatrixAffineSlice_isCompact U K c
  nonempty' := hne

/-- Helper for Exercise 9.9: every affine slice either is empty or admits the lower-dimensional
split cover supplied by the induction hypothesis. -/
lemma exists_affineSlice_split_cover {n C : ℕ}
    (hn : 0 < n)
    (hcover : SplitCoverProperty n C)
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hU : IsUnit U.det)
    (K : ConvexBody (Fin (n + 1) → ℝ))
    (hfree : ¬ K.ContainsIntegralPoint)
    (c : ℤ) :
    ∃ π : Fin C → {π : Fin n → ℤ // π ≠ 0},
      ∃ π₀ : Fin C → ℤ,
        integerMatrixAffineSlice U K c ⊆
          ⋃ i : Fin C, split_strip (π i).1 (π₀ i) := by
  by_cases hne : (integerMatrixAffineSlice U K c).Nonempty
  · let S : ConvexBody (Fin n → ℝ) :=
      integerMatrixAffineSliceConvexBody U K c hne
    have hSfree : ¬ S.ContainsIntegralPoint := by
      simpa [S, integerMatrixAffineSliceConvexBody] using
        integerMatrixAffineSlice_not_containsIntegralPoint U hU K hfree c
    exact hcover S hSfree
  · let π : Fin C → {π : Fin n → ℤ // π ≠ 0} :=
      fun _ ↦ ⟨standardIntegralDirection hn, standardIntegralDirection_ne_zero hn⟩
    refine ⟨π, fun _ ↦ 0, ?_⟩
    intro v hv
    exact False.elim (hne ⟨v, hv⟩)

/-- Helper for Exercise 9.9: a lower-dimensional integral direction lifted through the matrix
action, with its head coordinate set to zero. -/
def liftTailDirection {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (b : Fin n → ℤ) : Fin (n + 1) → ℤ :=
  (Fin.cons 0 b) ᵥ* U

/-- Helper for Exercise 9.9: inserting a zero head coefficient into a tail direction removes the
head coordinate from the split functional. -/
lemma split_dot_cons_zero_eq_tail {n : ℕ}
    (b : Fin n → ℤ)
    (y : Fin (n + 1) → ℝ) :
    split_dot (Fin.cons 0 b) y = split_dot b (Fin.tail y) := by
  rw [split_dot_eq_sum, split_dot_eq_sum, Fin.sum_univ_succ]
  simp [Fin.tail]

/-- Helper for Exercise 9.9: a lifted tail direction evaluates on `x` exactly as the original tail
direction evaluates on the matrix image of `x`. -/
lemma split_dot_liftTailDirection {n : ℕ}
    (U : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (b : Fin n → ℤ)
    (x : Fin (n + 1) → ℝ) :
    split_dot (liftTailDirection U b) x =
      split_dot (Fin.cons 0 b) (integerMatrixAction U x) := by
  have hcast :
      (fun j : Fin (n + 1) ↦ ((liftTailDirection U b) j : ℝ)) =
        (fun j : Fin (n + 1) ↦ ((Fin.cons 0 b : Fin (n + 1) → ℤ) j : ℝ)) ᵥ*
          U.map (Int.castRingHom ℝ) := by
    ext i
    exact RingHom.map_vecMul (Int.castRingHom ℝ) U (Fin.cons 0 b) i
  calc
    split_dot (liftTailDirection U b) x =
        (fun j : Fin (n + 1) ↦ ((liftTailDirection U b) j : ℝ)) ⬝ᵥ x := rfl
    _ =
        ((fun j : Fin (n + 1) ↦
          ((Fin.cons 0 b : Fin (n + 1) → ℤ) j : ℝ)) ᵥ*
            U.map (Int.castRingHom ℝ)) ⬝ᵥ x := by rw [hcast]
    _ =
        (fun j : Fin (n + 1) ↦
          ((Fin.cons 0 b : Fin (n + 1) → ℤ) j : ℝ)) ⬝ᵥ
            integerMatrixAction U x := by
      rw [← Matrix.dotProduct_mulVec]
      rfl
    _ = split_dot (Fin.cons 0 b) (integerMatrixAction U x) := rfl

/-- Helper for Exercise 9.9: lifting a nonzero tail direction through a matrix with a right
integral inverse remains nonzero. -/
lemma liftTailDirection_ne_zero {n : ℕ}
    (U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hUV : U * V = 1)
    (b : Fin n → ℤ)
    (hb : b ≠ 0) :
    liftTailDirection U b ≠ 0 := by
  intro hzero
  have hconsZero : (Fin.cons 0 b : Fin (n + 1) → ℤ) = 0 := by
    calc
      (Fin.cons 0 b : Fin (n + 1) → ℤ) =
          (Fin.cons 0 b) ᵥ* (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ) := by simp
      _ = (Fin.cons 0 b) ᵥ* (U * V) := by rw [hUV]
      _ = ((Fin.cons 0 b) ᵥ* U) ᵥ* V := by rw [Matrix.vecMul_vecMul]
      _ = 0 := by
        change liftTailDirection U b ᵥ* V = 0
        rw [hzero]
        simp
  apply hb
  funext i
  have htail := congrFun hconsZero i.succ
  simpa using htail

/-- Helper for Exercise 9.9: a nonzero lower-dimensional direction admits a nonzero ambient lift
with the same strip functional on the corresponding affine slice. -/
lemma exists_nonzero_liftTailDirection {n : ℕ}
    (U V : Matrix (Fin (n + 1)) (Fin (n + 1)) ℤ)
    (hUV : U * V = 1)
    (b : Fin n → ℤ)
    (hb : b ≠ 0) :
    ∃ w : Fin (n + 1) → ℤ,
      w ≠ 0 ∧
        ∀ x : Fin (n + 1) → ℝ,
          split_dot w x =
            split_dot (Fin.cons 0 b) (integerMatrixAction U x) := by
  refine ⟨liftTailDirection U b, liftTailDirection_ne_zero U V hUV b hb, ?_⟩
  intro x
  exact split_dot_liftTailDirection U b x

/-- Helper for Exercise 9.9: `split_dot` is the same linear form used in the lattice-width API. -/
lemma split_dot_eq_integral_direction_linear_form
    {n : ℕ}
    (d : Fin n → ℤ)
    (x : Fin n → ℝ) :
    split_dot d x = integral_direction_linear_form d x := by
  rfl

/-- Helper for Exercise 9.9: every point either already lies in the unit split strip determined by
its floor level, or else the split scalar product is exactly integral. -/
lemma mem_own_floor_split_strip_or_eq_floor
    {n : ℕ}
    (d : Fin n → ℤ)
    (x : Fin n → ℝ) :
    x ∈ split_strip d (Int.floor (split_dot d x)) ∨
      split_dot d x = (Int.floor (split_dot d x) : ℝ) := by
  by_cases hfloor : split_dot d x = (Int.floor (split_dot d x) : ℝ)
  · exact Or.inr hfloor
  · left
    rw [mem_split_strip_iff]
    refine ⟨?_, ?_⟩
    · -- Nonintegrality forces the split value to lie strictly above its floor.
      have hne : (Int.floor (split_dot d x) : ℝ) ≠ split_dot d x := by
        intro hEq
        exact hfloor hEq.symm
      exact lt_of_le_of_ne (Int.floor_le (split_dot d x)) hne
    · -- The standard floor estimate gives the upper unit-strip bound.
      exact Int.lt_floor_add_one (split_dot d x)

/-- Helper for Exercise 9.9: two split values attained on the same convex body differ by at most
the width `w_{d}(K)` in that direction. -/
lemma split_dot_sub_le_directional_width_of_mem
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ)
    {x y : Fin n → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K) :
    split_dot d x - split_dot d y ≤ w_{d}(K) := by
  let imageSet : Set ℝ := split_dot d '' K
  have hcont : Continuous fun z : Fin n → ℝ ↦ split_dot d z := by
    -- Rewrite the scalar product as a finite sum of coordinate maps to use standard continuity.
    have hsum : Continuous fun z : Fin n → ℝ ↦ ∑ i : Fin n, (d i : ℝ) * z i := by
      refine continuous_finsetSum _ ?_
      intro i hi
      exact continuous_const.mul (continuous_apply i)
    simpa [split_dot_eq_sum] using hsum
  have hcompact : IsCompact imageSet := by
    simpa [imageSet] using K.isCompact.image hcont
  have hx_image : split_dot d x ∈ imageSet := by
    exact ⟨x, hx, rfl⟩
  have hy_image : split_dot d y ∈ imageSet := by
    exact ⟨y, hy, rfl⟩
  have hx_le_sup : split_dot d x ≤ sSup imageSet := by
    exact le_csSup hcompact.bddAbove hx_image
  have hinf_le_y : sInf imageSet ≤ split_dot d y := by
    exact csInf_le hcompact.bddBelow hy_image
  have hwidth :
      split_dot d x - split_dot d y ≤ sSup imageSet - sInf imageSet := by
    linarith
  simpa [imageSet, directional_width, split_dot_eq_integral_direction_linear_form] using hwidth

/-- Helper for Exercise 9.9: bounded directional width controls all split values relative to any
chosen base point of the convex body. -/
lemma split_dot_abs_sub_le_of_directional_width_le
    {n : ℕ}
    (K : ConvexBody (Fin n → ℝ))
    (d : Fin n → ℤ)
    {x y : Fin n → ℝ}
    (hx : x ∈ K)
    (hy : y ∈ K)
    {W : ℝ}
    (hwidth : w_{d}(K) ≤ W) :
    |split_dot d x - split_dot d y| ≤ W := by
  have hxy :
      split_dot d x - split_dot d y ≤ w_{d}(K) :=
    split_dot_sub_le_directional_width_of_mem K d hx hy
  have hyx :
      split_dot d y - split_dot d x ≤ w_{d}(K) :=
    split_dot_sub_le_directional_width_of_mem K d hy hx
  have hneg : -w_{d}(K) ≤ split_dot d x - split_dot d y := by
    linarith
  have habs :
      |split_dot d x - split_dot d y| ≤ w_{d}(K) := by
    exact abs_le.2 ⟨hneg, hxy⟩
  exact le_trans habs hwidth

/-- Exercise 9.9. Every full-dimensional convex body in `ℝ^n` that contains no integral point is
contained in the union of `C n` open split strips, for a constant `C` depending only on the
dimension. The cover is indexed by genuine split directions, so each direction is a nonzero
integral vector. -/
theorem exists_open_split_cover_constant :
    ∃ C : ℕ → ℕ,
      ∀ {n : ℕ}, ∀ K : ConvexBody (Fin n → ℝ),
        K.FullDimensional →
        ¬ K.ContainsIntegralPoint →
        ∃ π : Fin (C n) → {π : Fin n → ℤ // π ≠ 0},
          ∃ π₀ : Fin (C n) → ℤ,
          (K : Set (Fin n → ℝ)) ⊆
            ⋃ i : Fin (C n), split_strip (π i).1 (π₀ i) := by
  classical
  have hcover : ∀ n : ℕ, ∃ c, SplitCoverProperty n c := by
    intro n
    induction n with
    | zero =>
        -- The zero-dimensional case is impossible under the lattice-free hypothesis.
        exact ⟨0, split_cover_property_zero_dimensional⟩
    | succ n ih =>
        cases n with
        | zero =>
            -- In dimension one, one split strip already covers the body.
            exact ⟨1, exists_single_open_split_cover_one_dimensional⟩
        | succ m =>
            rcases ih with ⟨Cm, hCm⟩
            obtain ⟨k, hk⟩ := exists_flatness_constant_for_lattice_width
            refine ⟨Nat.succ (Nat.ceil (k (m + 2))) * (Cm + 1), ?_⟩
            intro K hfree
            rcases K.nonempty with ⟨x₀, hx₀⟩
            have hdir :
                ∃ d : {d : Fin (m + 2) → ℤ // d ≠ 0},
                  w_{d.1}(K) ≤ k (m + 2) := by
              exact
                exists_bounded_flat_direction
                  (Nat.succ_pos (m + 1)) hk K hfree
            obtain ⟨d, hd⟩ := hdir
            obtain ⟨a, ha_ne, ha_gcd, ha_width⟩ :=
              exists_primitive_direction_le_width K d.1 d.2
            have ha_flat : w_{a}(K) ≤ k (m + 2) :=
              le_trans ha_width hd
            have hB : 0 ≤ k (m + 2) :=
              le_trans (directionalWidth_nonneg K a) ha_flat
            obtain ⟨L, hlevels⟩ :=
              exists_floor_window_of_split_dot_bound
                K a hx₀ hB ha_flat
            obtain ⟨U, V, hUV, hVU, hU, hrow⟩ :=
              exists_unimodular_matrix_with_first_row
                (Nat.succ_pos (m + 1)) a ha_gcd
            let B : ℝ := k (m + 2)
            let C : ℕ := Nat.ceil B
            have hlevelsC :
                ∀ x ∈ K, ∃ j : Fin (C + 1),
                  Int.floor (split_dot a x) = L + j := by
              simpa [B, C] using hlevels
            choose πj π₀j hπj using fun j : Fin (C + 1) ↦
              exists_affineSlice_split_cover
                (Nat.succ_pos m) hCm U hU K hfree (L + (j : ℤ))
            choose lifted hlift_ne hlift_eq using fun (j : Fin (C + 1))
                (i : Fin Cm) ↦
              exists_nonzero_liftTailDirection U V hUV
                (πj j i).1 (πj j i).2
            let directions :
                Fin (C + 1) × Fin (Cm + 1) →
                  {π : Fin (m + 2) → ℤ // π ≠ 0} :=
              fun p ↦
                Fin.cases ⟨a, ha_ne⟩
                  (fun i ↦ ⟨lifted p.1 i, hlift_ne p.1 i⟩) p.2
            let shifts : Fin (C + 1) × Fin (Cm + 1) → ℤ :=
              fun p ↦ Fin.cases (L + (p.1 : ℤ)) (fun i ↦ π₀j p.1 i) p.2
            let e : Fin (C + 1) × Fin (Cm + 1) ≃
                Fin ((C + 1) * (Cm + 1)) := finProdFinEquiv
            refine ⟨fun i ↦ directions (e.symm i),
              fun i ↦ shifts (e.symm i), ?_⟩
            intro x hxK
            let y : Fin (m + 2) → ℝ := integerMatrixAction U x
            have hy0 : y ⟨0, Nat.succ_pos (m + 1)⟩ = split_dot a x :=
              integerMatrixAction_zero_eq_split_dot
                (Nat.succ_pos (m + 1)) U a hrow x
            obtain ⟨j, hfloor⟩ := hlevelsC x hxK
            by_cases hinteger :
                split_dot a x = (Int.floor (split_dot a x) : ℝ)
            · -- At an integral projection value, use the recursive cover of the affine slice.
              have hlevel : split_dot a x = ((L + (j : ℤ) : ℤ) : ℝ) := by
                calc
                  split_dot a x = (Int.floor (split_dot a x) : ℝ) := hinteger
                  _ = ((L + (j : ℤ) : ℤ) : ℝ) := by rw [hfloor]
              have hyLevel : y ⟨0, Nat.succ_pos (m + 1)⟩ =
                  ((L + (j : ℤ) : ℤ) : ℝ) := by
                rw [hy0, hlevel]
              have htailMem :
                  Fin.tail y ∈ integerMatrixAffineSlice U K (L + (j : ℤ)) := by
                refine ⟨x, hxK, ?_⟩
                change integerMatrixAction U x =
                  Fin.cons ((L + (j : ℤ) : ℤ) : ℝ) (Fin.tail y)
                calc
                  integerMatrixAction U x = y := rfl
                  _ = Fin.cons (y ⟨0, Nat.succ_pos (m + 1)⟩) (Fin.tail y) :=
                    (Fin.cons_self_tail y).symm
                  _ = Fin.cons ((L + (j : ℤ) : ℤ) : ℝ) (Fin.tail y) :=
                    congrArg (fun t ↦ Fin.cons t (Fin.tail y)) hyLevel
              rcases Set.mem_iUnion.1 ((hπj j) htailMem) with ⟨i, hi⟩
              have hiAmbient :
                  x ∈ split_strip (lifted j i) (π₀j j i) := by
                rw [mem_split_strip_iff] at hi ⊢
                rw [hlift_eq j i x, split_dot_cons_zero_eq_tail]
                exact hi
              let p : Fin (C + 1) × Fin (Cm + 1) := ⟨j, Fin.succ i⟩
              refine Set.mem_iUnion.2 ⟨e p, ?_⟩
              change x ∈ split_strip (directions (e.symm (e p))).1
                (shifts (e.symm (e p)))
              rw [e.symm_apply_apply]
              simpa [directions, shifts] using hiAmbient
            · -- A nonintegral projection value lies in its own open unit strip.
              have hunit : x ∈ split_strip a (L + (j : ℤ)) := by
                rcases mem_own_floor_split_strip_or_eq_floor a x with hunit | hfloorEq
                · simpa [hfloor] using hunit
                · exact False.elim (hinteger hfloorEq)
              let p : Fin (C + 1) × Fin (Cm + 1) := ⟨j, 0⟩
              refine Set.mem_iUnion.2 ⟨e p, ?_⟩
              change x ∈ split_strip (directions (e.symm (e p))).1
                (shifts (e.symm (e p)))
              rw [e.symm_apply_apply]
              simpa [directions, shifts] using hunit
  refine ⟨fun n ↦ Classical.choose (hcover n), ?_⟩
  intro n K hfull hfree
  exact Classical.choose_spec (hcover n) K hfree

end Exercise99

#print axioms exists_open_split_cover_constant
