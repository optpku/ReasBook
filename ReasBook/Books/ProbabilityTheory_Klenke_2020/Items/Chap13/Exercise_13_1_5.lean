/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Data.Set.FiniteExhaustion
public import Mathlib.MeasureTheory.Covering.Vitali
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Data.Set.Defs
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Real
public import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Topology.Bornology.Basic
public import Mathlib.Topology.Bases

public section

open scoped BigOperators Pointwise Topology
open MeasureTheory Set

-- Semantic recall note: the general Vitali covering API comes from
-- `Vitali.exists_disjoint_subfamily_covering_enlargement`. The helper theorem
-- `disjoint_selection_of_originSymmetric_model` records the supported origin-symmetric common-model
-- variant used elsewhere in this file.

/-- An open, bounded, convex subset of `(Fin d → ℝ)`. -/
def IsOpenBoundedConvexSet {d : ℕ} (C : Set (Fin d → ℝ)) : Prop :=
  IsOpen C ∧ Bornology.IsBounded C ∧ Convex ℝ C

/-- A family of open, bounded, convex subsets of `(Fin d → ℝ)`. -/
def IsOpenBoundedConvexFamily {d : ℕ} (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  ∀ U ∈ 𝒰, IsOpenBoundedConvexSet U

/-- `U` is a positive homothetic copy of `C`. -/
def IsPositiveHomotheticCopyOf {d : ℕ} (C U : Set (Fin d → ℝ)) : Prop :=
  ∃ x : Fin d → ℝ, ∃ r : ℝ, 0 < r ∧ U = ({x} : Set (Fin d → ℝ)) + r • C

/-- The family consists of positive homothetic copies of the fixed set `C`. -/
def IsPositiveHomotheticCopyFamilyOf {d : ℕ} (C : Set (Fin d → ℝ))
    (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  ∀ U ∈ 𝒰, IsPositiveHomotheticCopyOf C U

/-- `C` is centrally symmetric with respect to the origin. -/
def IsOriginSymmetric {d : ℕ} (C : Set (Fin d → ℝ)) : Prop :=
  ∀ ⦃x : Fin d → ℝ⦄, x ∈ C → -x ∈ C

/-- The family consists of positive homothetic copies of one fixed open, bounded, convex set. -/
def HasCommonHomotheticModel {d : ℕ} (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  ∃ C : Set (Fin d → ℝ),
    IsOpenBoundedConvexSet C ∧ IsPositiveHomotheticCopyFamilyOf C 𝒰

/-- The family consists of positive homothetic copies of one fixed open, bounded, convex,
origin-symmetric set. -/
def HasCommonCentrallySymmetricModel {d : ℕ} (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  ∃ C : Set (Fin d → ℝ),
    IsOpenBoundedConvexSet C ∧ IsOriginSymmetric C ∧ IsPositiveHomotheticCopyFamilyOf C 𝒰

/-- `C` is a common open bounded convex model for `𝒰`, but it is not origin-symmetric. -/
def IsAsymmetricCommonHomotheticModel {d : ℕ} (C : Set (Fin d → ℝ))
    (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  IsOpenBoundedConvexSet C ∧
    ¬ IsOriginSymmetric C ∧
    IsPositiveHomotheticCopyFamilyOf C 𝒰

/-- The union of the family has finite Lebesgue measure. -/
def HasFiniteUnionMeasure {d : ℕ} (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  volume (⋃₀ 𝒰) < ⊤

/-- The finite disjoint subfamily conclusion printed in the first sentence of this exercise item. -/
def HasLargeMeasureSelection {d : ℕ} (𝒰 : Set (Set (Fin d → ℝ))) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∃ s : Finset (Set (Fin d → ℝ)),
      (∀ ⦃U : Set (Fin d → ℝ)⦄, U ∈ s → U ∈ 𝒰) ∧
      (∀ ⦃U V : Set (Fin d → ℝ)⦄, U ∈ s → V ∈ s → U ≠ V → Disjoint U V) ∧
      ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) < s.sum (fun U ↦ volume.real U)

/-- Helper for Exercise 13.1.5: a nonempty convex origin-symmetric set contains `0`. -/
private lemma zero_mem_of_nonempty_of_convex_of_originSymmetric {d : ℕ}
    {C : Set (Fin d → ℝ)} (hC_convex : Convex ℝ C) (hC_symm : IsOriginSymmetric C)
    (hC_nonempty : C.Nonempty) : (0 : Fin d → ℝ) ∈ C := by
  -- Proof comment: midpoint convexity applied to `x` and `-x` forces the origin into `C`.
  rcases hC_nonempty with ⟨x, hx⟩
  have hneg : -x ∈ C := hC_symm hx
  have hmid : (1 / 2 : ℝ) • x + (1 / 2 : ℝ) • (-x) ∈ C :=
    hC_convex hx hneg (by positivity) (by positivity) (by norm_num)
  simpa using hmid

/-- Helper for Exercise 13.1.5: translated dilates have the expected Lebesgue volume. -/
private lemma translatedSmul_volume {d : ℕ} {C : Set (Fin d → ℝ)}
    (x : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (({x} : Set (Fin d → ℝ)) + r • C) = ENNReal.ofReal (r ^ d) * volume C := by
  -- Proof comment: translation invariance removes the center, and Haar scaling computes the
  -- remaining positive homothety in `ENNReal`.
  calc
    volume (({x} : Set (Fin d → ℝ)) + r • C)
        = volume (r • C) := by
            have h :=
              measure_preimage_add_right volume x
                ((fun y : Fin d → ℝ ↦ x + y) '' (r • C))
            rw [singleton_add]
            have hpreimage :
                (fun z : Fin d → ℝ ↦ z + x) ⁻¹' ((fun y : Fin d → ℝ ↦ x + y) '' (r • C)) =
                  r • C := by
              ext z
              constructor
              · rintro ⟨y, hy, hyz⟩
                have hz : z = y := by simpa [add_comm] using hyz.symm
                simpa [hz] using hy
              · intro hz
                exact ⟨z, hz, by simp [add_comm]⟩
            calc
              volume ((fun y : Fin d → ℝ ↦ x + y) '' (r • C)) =
                  volume
                    ((fun z : Fin d → ℝ ↦ z + x) ⁻¹' ((fun y : Fin d → ℝ ↦ x + y) '' (r • C))) :=
                    h.symm
              _ = volume (r • C) := by rw [hpreimage]
    _ = ENNReal.ofReal (r ^ d) * volume C := by
      convert Measure.addHaar_smul_of_nonneg volume hr C using 1
      simp

/-- Helper for Exercise 13.1.5: translated dilates have the expected Lebesgue volume. -/
private lemma translatedSmul_volumeReal {d : ℕ} {C : Set (Fin d → ℝ)}
    (_hC_meas : MeasurableSet C) (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    volume.real (({x} : Set (Fin d → ℝ)) + r • C) = r ^ d * volume.real C := by
  -- Proof comment: translation invariance removes the center, then the Haar scaling law handles
  -- the positive homothety factor.
  have hvol : volume (({x} : Set (Fin d → ℝ)) + r • C) =
      ENNReal.ofReal (r ^ d) * volume C :=
    @translatedSmul_volume d C x r hr.le
  rw [measureReal_def, hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr.le _),
    measureReal_def]

/-- Helper for Exercise 13.1.5: an open bounded set containing `0` has positive Lebesgue volume. -/
private lemma volumeReal_pos_of_open_of_mem_zero {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C) (hC_zero : (0 : Fin d → ℝ) ∈ C) :
    0 < volume.real C := by
  -- Proof comment: openness gives positive Haar measure around the interior point `0`, while
  -- boundedness guarantees that the real-valued measure is finite.
  refine ENNReal.toReal_pos (hC_open.measure_pos volume ⟨0, hC_zero⟩).ne' ?_
  exact hC_bounded.measure_lt_top.ne

/-- Helper for Exercise 13.1.5: an open bounded nonempty set has positive Lebesgue volume. -/
private lemma volumeReal_pos_of_open_of_bounded_of_nonempty {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C) (hC_nonempty : C.Nonempty) :
    0 < volume.real C := by
  -- Proof comment: openness gives positive measure at any interior point, while boundedness keeps
  -- the real-valued measure finite.
  rcases hC_nonempty with ⟨x, hx⟩
  refine ENNReal.toReal_pos (hC_open.measure_pos volume ⟨x, hx⟩).ne' ?_
  exact hC_bounded.measure_lt_top.ne

/-- Helper for Exercise 13.1.5: differences of two points in a convex origin-symmetric model lie in
the doubled model. -/
private lemma sub_mem_twoSmul_of_mem_model {d : ℕ} {C : Set (Fin d → ℝ)}
    (hC_convex : Convex ℝ C) (hC_symm : IsOriginSymmetric C) {a b : Fin d → ℝ}
    (ha : a ∈ C) (hb : b ∈ C) :
    a - b ∈ (2 : ℝ) • C := by
  -- Proof comment: `a - b` is twice the midpoint of `a` and `-b`, and that midpoint lies in `C`.
  have hneg : -b ∈ C := hC_symm hb
  have hmid : (1 / 2 : ℝ) • a + (1 / 2 : ℝ) • (-b) ∈ C :=
    hC_convex ha hneg (by positivity) (by positivity) (by norm_num)
  refine ⟨(1 / 2 : ℝ) • a + (1 / 2 : ℝ) • (-b), hmid, ?_⟩
  simp [sub_eq_add_neg, smul_add, smul_smul]

/-- Helper for Exercise 13.1.5: membership in a translated dilate is equivalent to an explicit
pointwise representation. -/
private lemma mem_singleton_add_smul_iff {d : ℕ} {C : Set (Fin d → ℝ)}
    {x z : Fin d → ℝ} {r : ℝ} :
    z ∈ ({x} : Set (Fin d → ℝ)) + r • C ↔ ∃ c ∈ C, z = x + r • c := by
  -- Proof comment: unpack set addition and scalar-action membership once so later geometric
  -- arguments can work directly with points of `C`.
  constructor
  · intro hz
    rcases hz with ⟨u, hu, v, hv, huv⟩
    rcases hu with rfl
    rcases hv with ⟨c, hc, rfl⟩
    exact ⟨c, hc, huv.symm⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨x, by simp, r • c, ?_, rfl⟩
    exact ⟨c, hc, rfl⟩

/-- Helper for Exercise 13.1.5: a point of the form `b + η • (c - a)` stays inside the enlarged
model copy whenever `a`, `b`, and `c` lie in `C` and `0 ≤ η ≤ τ`. -/
private lemma mem_enlargedModel_of_mem_of_mem_of_mem_of_le {d : ℕ}
    {C : Set (Fin d → ℝ)} (hC_convex : Convex ℝ C) (hC_symm : IsOriginSymmetric C)
    {a b c : Fin d → ℝ} (ha : a ∈ C) (hb : b ∈ C) (hc : c ∈ C) {η τ : ℝ}
    (hη : 0 ≤ η) (hητ : η ≤ τ) :
    b + η • (c - a) ∈ (((1 + 2 * τ) : ℝ) • C) := by
  -- Proof comment: the error term `η • (c - a)` lives in a `(2τ)`-dilate of `C`, and convexity
  -- combines this with `b ∈ C` into one `(1 + 2τ)`-dilate.
  have hC_nonempty : C.Nonempty := ⟨b, hb⟩
  have hzero : (0 : Fin d → ℝ) ∈ C :=
    zero_mem_of_nonempty_of_convex_of_originSymmetric hC_convex hC_symm hC_nonempty
  have hb_mem : b ∈ (1 : ℝ) • C := by
    simpa using
      (show (1 : ℝ) • b ∈ (1 : ℝ) • C from Set.smul_mem_smul_set hb)
  have hsub : c - a ∈ (2 : ℝ) • C := sub_mem_twoSmul_of_mem_model hC_convex hC_symm hc ha
  have hscaled :
      η • (c - a) ∈ ((2 * τ) : ℝ) • C := by
    have hτ : 0 ≤ τ := le_trans hη hητ
    by_cases hτ_zero : τ = 0
    · have hη_zero : η = 0 := le_antisymm (by simpa [hτ_zero] using hητ) hη
      subst hτ_zero
      subst hη_zero
      simpa using
        (show (0 : ℝ) • (0 : Fin d → ℝ) ∈ (0 : ℝ) • C from Set.smul_mem_smul_set hzero)
    · rcases hsub with ⟨z, hzC, hzEq⟩
      have hτ_pos : 0 < τ := lt_of_le_of_ne hτ (by simpa [eq_comm] using hτ_zero)
      have hratio : η / τ ∈ Set.Icc (0 : ℝ) 1 := by
        refine ⟨div_nonneg hη hτ, ?_⟩
        exact (div_le_iff₀ hτ_pos).2 (by simpa using hητ)
      have hz_small : (η / τ) • z ∈ C :=
        hC_convex.smul_mem_of_zero_mem hzero hzC hratio
      have hrewrite : η • (c - a) = (2 * τ : ℝ) • ((η / τ) • z) := by
        calc
          η • (c - a) = η • ((2 : ℝ) • z) := by
            simpa using congrArg (fun t : Fin d → ℝ ↦ η • t) hzEq.symm
          _ = (2 * η : ℝ) • z := by
            rw [smul_smul]
            ring
          _ = ((2 * τ) * (η / τ) : ℝ) • z := by
            congr 1
            field_simp [hτ_zero]
          _ = (2 * τ : ℝ) • ((η / τ) • z) := by rw [smul_smul]
      have : (2 * τ : ℝ) • ((η / τ) • z) ∈ ((2 * τ) : ℝ) • C := smul_mem_smul_set hz_small
      exact hrewrite ▸ this
  have hsum :
      b + η • (c - a) ∈ (1 : ℝ) • C + ((2 * τ) : ℝ) • C := by
    exact ⟨b, hb_mem, η • (c - a), hscaled, rfl⟩
  have hadd :
      ((1 + 2 * τ) : ℝ) • C = (1 : ℝ) • C + ((2 * τ) : ℝ) • C := by
    have htwoτ : 0 ≤ 2 * τ := by nlinarith [hη, hητ]
    simpa using
      (show (((1 : ℝ) + (2 * τ)) • C) = (1 : ℝ) • C + ((2 * τ) : ℝ) • C from
        hC_convex.add_smul (show 0 ≤ (1 : ℝ) by positivity) htwoτ)
  simpa [hadd] using hsum

/-- Helper for Exercise 13.1.5: overlapping homothetic copies with comparable scales are contained
in a fixed enlargement of the larger copy. -/
private lemma subset_enlargedCopy_of_inter_nonempty_of_scale_le {d : ℕ}
    {C : Set (Fin d → ℝ)} (hC_convex : Convex ℝ C) (hC_symm : IsOriginSymmetric C)
    {x y : Fin d → ℝ} {r s τ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hinter : ((({x} : Set (Fin d → ℝ)) + r • C) ∩ (({y} : Set (Fin d → ℝ)) + s • C)).Nonempty)
    (hscale : r ≤ τ * s) :
    (({x} : Set (Fin d → ℝ)) + r • C) ⊆
      ({y} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * s) • C) := by
  -- Proof comment: intersection gives a bridge point `x + r a = y + s b`; after rewriting
  -- `x + r c`, convexity and symmetry package the error term into one `(1 + 2τ)`-dilate of `C`.
  intro u hu
  rcases hinter with ⟨z, hz⟩
  rcases mem_singleton_add_smul_iff.mp hz.1 with ⟨a, ha, hza⟩
  rcases mem_singleton_add_smul_iff.mp hz.2 with ⟨b, hb, hzb⟩
  rcases mem_singleton_add_smul_iff.mp hu with ⟨c, hc, huc⟩
  let η : ℝ := r / s
  have hη : 0 ≤ η := by
    dsimp [η]
    exact div_nonneg hr.le hs.le
  have hητ : η ≤ τ := by
    dsimp [η]
    exact (div_le_iff₀ hs).2 hscale
  have hbridge : x + r • a = y + s • b := by
    rw [← hza, hzb]
  have hsdiv : s • (η • (c - a)) = r • (c - a) := by
    dsimp [η]
    rw [smul_smul]
    congr 1
    field_simp [hs.ne']
  have hu_eq : u = y + s • (b + η • (c - a)) := by
    calc
      u = x + r • c := huc
      _ = (x + r • a) + r • (c - a) := by
        simp [sub_eq_add_neg, smul_add, add_assoc]
      _ = (y + s • b) + r • (c - a) := by rw [hbridge]
      _ = y + s • b + r • (c - a) := by simp [add_assoc]
      _ = y + s • b + s • (η • (c - a)) := by rw [← hsdiv]
      _ = y + s • (b + η • (c - a)) := by
        rw [smul_add]
        simp [add_assoc]
  have hmodel :
      b + η • (c - a) ∈ (((1 + 2 * τ) : ℝ) • C) :=
    mem_enlargedModel_of_mem_of_mem_of_mem_of_le hC_convex hC_symm ha hb hc hη hητ
  refine ⟨y, by simp, s • (b + η • (c - a)), ?_, hu_eq.symm⟩
  simpa [smul_smul, mul_comm, mul_left_comm, mul_assoc, smul_add, smul_sub] using
    (show s • (b + η • (c - a)) ∈ s • (((1 + 2 * τ) : ℝ) • C) from Set.smul_mem_smul_set hmodel)

/-- Helper for Exercise 13.1.5: one can choose an enlargement factor arbitrarily close to `3^d`
from above. -/
private lemma exists_almostThree_enlargementFactor {d : ℕ} {ε : ℝ}
    (hε : 0 < ε) (hε_lt_one : ε < 1) :
    ∃ τ > 1, ((1 + 2 * τ) : ℝ) ^ d < (3 : ℝ) ^ d / (1 - ε) := by
  -- Proof comment: the map `τ ↦ (1 + 2τ)^d` is continuous, so an open upper bound at `τ = 1`
  -- persists for all sufficiently close right-neighbors.
  let rhs : ℝ := (3 : ℝ) ^ d / (1 - ε)
  have hthree_lt_rhs : (3 : ℝ) ^ d < rhs := by
    have hden_pos : 0 < 1 - ε := sub_pos.mpr hε_lt_one
    refine (lt_div_iff₀ hden_pos).2 ?_
    have hpow_pos : 0 < (3 : ℝ) ^ d := by positivity
    nlinarith
  have hcont : Continuous fun τ : ℝ ↦ ((1 + 2 * τ) : ℝ) ^ d := by
    continuity
  have hEventually :
      ∀ᶠ τ : ℝ in nhdsWithin (1 : ℝ) (Set.Ioi 1), ((1 + 2 * τ) : ℝ) ^ d < rhs := by
    let S : Set ℝ := {τ : ℝ | ((1 + 2 * τ) : ℝ) ^ d < rhs}
    have hS_open : IsOpen S := isOpen_lt hcont continuous_const
    have hS_mem : (1 : ℝ) ∈ S := by
      change ((1 + 2 * (1 : ℝ)) : ℝ) ^ d < rhs
      norm_num
      simpa using hthree_lt_rhs
    exact mem_nhdsWithin_of_mem_nhds (hS_open.mem_nhds hS_mem)
  obtain ⟨τ, hτbound, hτgt⟩ := (hEventually.and self_mem_nhdsWithin).exists
  exact ⟨τ, hτgt, hτbound⟩

/-- Helper for Exercise 13.1.5: a countable pairwise disjoint measurable family with finite union
measure admits a finite subfamily whose measure sum is above any smaller real target. -/
private lemma existsFinset_sum_gt_of_lt_volumeReal_sUnion {d : ℕ}
    {u : Set (Set (Fin d → ℝ))} (hu_count : u.Countable) (hu_disj : u.PairwiseDisjoint id)
    (hu_meas : ∀ U ∈ u, MeasurableSet U) (hu_fin : volume (⋃₀ u) < ⊤)
    {c : ℝ} (hc : c < volume.real (⋃₀ u)) :
    ∃ s : Finset (Set (Fin d → ℝ)),
      (s : Set (Set (Fin d → ℝ))) ⊆ u ∧
      (s : Set (Set (Fin d → ℝ))).PairwiseDisjoint id ∧
      c < s.sum (fun U ↦ volume.real U) := by
  classical
  -- Proof comment: exhaust the countable family by finite stages and use continuity from below of
  -- measure to pass from the countable disjoint union to one sufficiently large finite stage.
  let K := hu_count.finiteExhaustion
  have hK_subset (n : ℕ) : K n ⊆ u := by
    intro U hU
    have : U ∈ ⋃ n, K n := mem_iUnion.2 ⟨n, hU⟩
    simpa [K.iUnion_eq] using this
  have hK_union : (⋃ n, ⋃₀ K n) = ⋃₀ u := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨n, hx⟩
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      exact mem_sUnion.2 ⟨U, hK_subset n hU, hxU⟩
    · intro hx
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      have : U ∈ ⋃ n, K n := by simpa [K.iUnion_eq] using hU
      rcases mem_iUnion.1 this with ⟨n, hU_n⟩
      exact mem_iUnion.2 ⟨n, mem_sUnion.2 ⟨U, hU_n, hxU⟩⟩
  have hK_mono : Monotone fun n ↦ ⋃₀ K n := by
    intro m n hmn
    exact sUnion_subset_sUnion (K.mono hmn)
  have hK_tendsto_enn :
      Filter.Tendsto (fun n ↦ volume (⋃₀ K n)) Filter.atTop (nhds (volume (⋃₀ u))) := by
    simpa [hK_union] using (tendsto_measure_iUnion_atTop hK_mono)
  have hK_tendsto :
      Filter.Tendsto (fun n ↦ volume.real (⋃₀ K n)) Filter.atTop (nhds (volume.real (⋃₀ u))) := by
    rw [← ENNReal.tendsto_toReal_iff
      (fun n ↦ ne_top_of_le_ne_top hu_fin.ne (measure_mono (sUnion_subset_sUnion (hK_subset n))))
      hu_fin.ne] at hK_tendsto_enn
    simpa [Measure.real_def] using hK_tendsto_enn
  have hδ : 0 < volume.real (⋃₀ u) - c := sub_pos.mpr hc
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hK_tendsto (volume.real (⋃₀ u) - c) hδ
  have hstage_le : volume.real (⋃₀ K N) ≤ volume.real (⋃₀ u) := by
    exact measureReal_mono (sUnion_subset_sUnion (hK_subset N)) hu_fin.ne
  have hdist : dist (volume.real (⋃₀ u)) (volume.real (⋃₀ K N)) < volume.real (⋃₀ u) - c := by
    simpa [dist_comm] using hN N le_rfl
  have hstage_gt : c < volume.real (⋃₀ K N) := by
    have hdiff :
        volume.real (⋃₀ u) - volume.real (⋃₀ K N) < volume.real (⋃₀ u) - c := by
      simpa [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hstage_le)] using hdist
    linarith
  let s : Finset (Set (Fin d → ℝ)) := (K.finite N).toFinset
  have hs_eq : (s : Set (Set (Fin d → ℝ))) = K N := by
    ext U
    simp [s]
  have hs_subset : (s : Set (Set (Fin d → ℝ))) ⊆ u := by
    intro U hU
    exact hK_subset N (by simpa [hs_eq] using hU)
  have hs_disj : (s : Set (Set (Fin d → ℝ))).PairwiseDisjoint id := hu_disj.subset hs_subset
  have hs_mem_fin : ∀ U ∈ s, volume U ≠ ⊤ := by
    intro U hU
    exact ne_top_of_le_ne_top hu_fin.ne
      (measure_mono (subset_sUnion_of_mem (hs_subset (by simpa using hU))))
  have hs_sum :
      volume.real (⋃₀ K N) = s.sum (fun U ↦ volume.real U) := by
    rw [← hs_eq]
    rw [Set.sUnion_eq_biUnion]
    exact measureReal_biUnion_finset hs_disj
      (fun U hU ↦ hu_meas U (hs_subset (by simpa using hU))) hs_mem_fin
  exact ⟨s, hs_subset, hs_disj, by simpa [hs_sum] using hstage_gt⟩

/-- Helper for Exercise 13.1.5: package the homothetic-copy data on the subtype of actual family
members, so later rewrites no longer depend on explicit membership proofs. -/
private lemma existsSubtypeCopyData {d : ℕ} {C : Set (Fin d → ℝ)}
    {𝒰 : Set (Set (Fin d → ℝ))} (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰) :
    ∃ center : {U : Set (Fin d → ℝ) // U ∈ 𝒰} → Fin d → ℝ,
      ∃ scale : {U : Set (Fin d → ℝ) // U ∈ 𝒰} → ℝ,
        (∀ U, 0 < scale U) ∧
        ∀ U, U.1 = ({center U} : Set (Fin d → ℝ)) + scale U • C := by
  classical
  choose center scale hscale hcopy using hfamily
  refine ⟨fun U ↦ center U.1 U.2, fun U ↦ scale U.1 U.2, ?_⟩
  constructor
  · -- Proof comment: the positivity witnesses are inherited pointwise from the family hypothesis.
    intro U
    exact hscale U.1 U.2
  · -- Proof comment: each subtype member keeps the same center/scale decomposition as the
    -- original family member.
    intro U
    exact hcopy U.1 U.2

/-- Helper for Exercise 13.1.5: Vitali's abstract selection theorem yields a countable disjoint
subfamily of the subtype-indexed copy family whose members dominate all family members in real
volume up to the factor `τ ^ d`. -/
private lemma existsCountableDisjointCoveringSubfamily {d : ℕ}
    {C : Set (Fin d → ℝ)} {𝒰 : Set (Set (Fin d → ℝ))}
    (hd : d ≠ 0) (hC_open : IsOpen C) (hC_nonempty : C.Nonempty)
    (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰) (h𝒰_fin : volume (⋃₀ 𝒰) < ⊤)
    {τ : ℝ} (hτ : 1 < τ) :
    ∃ u : Set {U : Set (Fin d → ℝ) // U ∈ 𝒰},
      u.PairwiseDisjoint (fun U ↦ U.1) ∧
      u.Countable ∧
      ∀ U : {U : Set (Fin d → ℝ) // U ∈ 𝒰},
        ∃ V ∈ u, (U.1 ∩ V.1).Nonempty ∧ volume.real U.1 ≤ τ ^ d * volume.real V.1 := by
  classical
  let ι := {U : Set (Fin d → ℝ) // U ∈ 𝒰}
  obtain ⟨center, scale, hscale_pos, hcopy_eq⟩ := existsSubtypeCopyData hfamily
  have hmember_nonempty : ∀ U : ι, U.1.Nonempty := by
    -- Proof comment: a positive copy of a nonempty model is nonempty.
    intro U
    rcases hC_nonempty with ⟨c, hc⟩
    rw [hcopy_eq U]
    exact ⟨center U + scale U • c, mem_singleton_add_smul_iff.mpr ⟨c, hc, rfl⟩⟩
  have hmember_open : ∀ U : ι, IsOpen U.1 := by
    -- Proof comment: every family member is a translate of a positive dilate of the open model.
    intro U
    rw [hcopy_eq U, singleton_add]
    exact (Homeomorph.addLeft (center U)).isOpenMap _ (hC_open.smul₀ (hscale_pos U).ne')
  obtain ⟨u, _, hu_disj, hu_cover⟩ :=
    Vitali.exists_disjoint_subfamily_covering_enlargement
      (fun U : ι ↦ U.1) Set.univ (fun U ↦ volume.real U.1) (τ ^ d) (one_lt_pow₀ hτ hd)
      (fun U _ ↦ measureReal_nonneg) (volume.real (⋃₀ 𝒰))
      (fun U _ ↦ measureReal_mono (subset_sUnion_of_mem U.2) h𝒰_fin.ne)
      (fun U _ ↦ hmember_nonempty U)
  have hu_count : u.Countable := by
    -- Proof comment: a pairwise disjoint family of open nonempty subsets of a separable space is
    -- countable.
    exact hu_disj.countable_of_nonempty_interior fun U hU ↦ by
      simpa [hmember_open U, hmember_open U |>.interior_eq] using hmember_nonempty U
  refine ⟨u, hu_disj, hu_count, ?_⟩
  -- Proof comment: the Vitali covering relation is already expressed on the subtype family, so no
  -- further transport is needed here.
  intro U
  exact hu_cover U (by simp)

/-- Helper for Exercise 13.1.5: a subtype-indexed Vitali-selected subfamily controls the whole
union after enlarging each selected copy by the fixed factor `(1 + 2τ)`. -/
private lemma measure_sUnion_le_scaledSelection {d : ℕ}
    {C : Set (Fin d → ℝ)} {𝒰 : Set (Set (Fin d → ℝ))}
    (hd : d ≠ 0) (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C)
    (hC_convex : Convex ℝ C) (hC_symm : IsOriginSymmetric C)
    (hC_zero : (0 : Fin d → ℝ) ∈ C)
    (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰) (h𝒰_fin : volume (⋃₀ 𝒰) < ⊤)
    {u : Set {U : Set (Fin d → ℝ) // U ∈ 𝒰}} (hu_count : u.Countable)
    (hu_disj : u.PairwiseDisjoint (fun U ↦ U.1)) {τ : ℝ} (hτ : 1 < τ)
    (hcover :
      ∀ U : {U : Set (Fin d → ℝ) // U ∈ 𝒰},
        ∃ V ∈ u, (U.1 ∩ V.1).Nonempty ∧ volume.real U.1 ≤ τ ^ d * volume.real V.1) :
    volume.real (⋃₀ 𝒰) ≤ ((1 + 2 * τ) : ℝ) ^ d * volume.real (⋃₀ (Subtype.val '' u)) := by
  classical
  let ι := {U : Set (Fin d → ℝ) // U ∈ 𝒰}
  obtain ⟨center, scale, hscale_pos, hcopy_eq⟩ := existsSubtypeCopyData hfamily
  have hC_vol_pos : 0 < volume.real C :=
    volumeReal_pos_of_open_of_mem_zero hC_open hC_bounded hC_zero
  have hmember_open : ∀ U : ι, IsOpen U.1 := by
    -- Proof comment: the copy description turns every family member into a translate of an open
    -- positive dilate of `C`.
    intro U
    rw [hcopy_eq U, singleton_add]
    exact (Homeomorph.addLeft (center U)).isOpenMap _ (hC_open.smul₀ (hscale_pos U).ne')
  have hmember_meas : ∀ U : ι, MeasurableSet U.1 := by
    intro U
    exact (hmember_open U).measurableSet
  have hmember_volumeReal : ∀ U : ι, volume.real U.1 = scale U ^ d * volume.real C := by
    -- Proof comment: each family member has the model volume multiplied by the `d`-th power of
    -- its scale.
    intro U
    rw [hcopy_eq U]
    simpa using
      (@translatedSmul_volumeReal d C hC_open.measurableSet (center U) (scale U) (hscale_pos U))
  have hcover_subset :
      ⋃₀ 𝒰 ⊆ ⋃ V : u, ({center V.1} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V.1) • C) := by
    -- Proof comment: every original member intersects a selected one of comparable volume, and
    -- the geometric enlargement lemma upgrades that relation to actual set containment.
    intro x hx
    rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
    rcases hcover ⟨U, hU⟩ with ⟨V, hV, hinter, hvol⟩
    have hτ_nonneg : 0 ≤ τ := le_trans zero_lt_one.le hτ.le
    have hvol' : scale ⟨U, hU⟩ ^ d * volume.real C ≤ τ ^ d * (scale V ^ d * volume.real C) := by
      rw [hmember_volumeReal ⟨U, hU⟩, hmember_volumeReal V] at hvol
      exact hvol
    have hpow_mul :
        scale ⟨U, hU⟩ ^ d * volume.real C ≤ (τ * scale V) ^ d * volume.real C := by
      calc
        scale ⟨U, hU⟩ ^ d * volume.real C ≤ τ ^ d * (scale V ^ d * volume.real C) := hvol'
        _ = (τ ^ d * scale V ^ d) * volume.real C := by ring
        _ = (τ * scale V) ^ d * volume.real C := by rw [mul_pow]
    have hpow_le : scale ⟨U, hU⟩ ^ d ≤ (τ * scale V) ^ d := by
      nlinarith
    have hscale :
        scale ⟨U, hU⟩ ≤ τ * scale V := by
      exact (pow_le_pow_iff_left₀ (hscale_pos ⟨U, hU⟩).le
        (mul_nonneg hτ_nonneg (hscale_pos V).le) hd).mp hpow_le
    have hinter' :
        ((({center ⟨U, hU⟩} : Set (Fin d → ℝ)) + scale ⟨U, hU⟩ • C) ∩
          (({center V} : Set (Fin d → ℝ)) + scale V • C)).Nonempty := by
      rw [hcopy_eq ⟨U, hU⟩, hcopy_eq V] at hinter
      exact hinter
    have hsubset :
        U ⊆ ({center V} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V) • C) := by
      have hsubset' :
          (({center ⟨U, hU⟩} : Set (Fin d → ℝ)) + scale ⟨U, hU⟩ • C) ⊆
            ({center V} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V) • C) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          subset_enlargedCopy_of_inter_nonempty_of_scale_le hC_convex hC_symm
            (hscale_pos ⟨U, hU⟩) (hscale_pos V) hinter' hscale
      intro y hy
      have hU_eq :
          U = ({center ⟨U, hU⟩} : Set (Fin d → ℝ)) + scale ⟨U, hU⟩ • C := hcopy_eq ⟨U, hU⟩
      have hy' := hy
      rw [hU_eq] at hy'
      exact hsubset' hy'
    exact mem_iUnion.2 ⟨⟨V, hV⟩, hsubset hxU⟩
  have himage_union :
      (⋃ V : u, V.1.1) = ⋃₀ (Subtype.val '' u) := by
    ext x
    constructor
    · intro hx
      rcases mem_iUnion.1 hx with ⟨V, hxV⟩
      exact mem_sUnion.2 ⟨V.1.1, ⟨V.1, V.2, rfl⟩, hxV⟩
    · intro hx
      rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
      rcases hU with ⟨V, hV, rfl⟩
      exact mem_iUnion.2 ⟨⟨V, hV⟩, hxU⟩
  have hsubtype_disj : Pairwise fun V W : u ↦ Disjoint V.1.1 W.1.1 := by
    intro V W hVW
    exact hu_disj V.2 W.2 fun h ↦ hVW (Subtype.ext h)
  have hmeasure_member :
      ∀ V : u,
        volume (({center V.1} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V.1) • C)) =
          ENNReal.ofReal (((1 + 2 * τ : ℝ) ^ d)) * volume V.1.1 := by
    -- Proof comment: enlarging a selected copy multiplies its volume by the fixed factor
    -- `((1 + 2τ) ^ d)`.
    intro V
    have hvolV : volume V.1.1 = ENNReal.ofReal ((scale V.1) ^ d) * volume C := by
      simpa [hcopy_eq V.1] using translatedSmul_volume (center V.1) (hscale_pos V.1).le
    have hfactor_pos : 0 < (1 + 2 * τ : ℝ) := by linarith
    calc
      volume (({center V.1} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V.1) • C))
          = ENNReal.ofReal ((((1 + 2 * τ) * scale V.1) ^ d)) * volume C := by
              simpa using translatedSmul_volume (center V.1)
                (mul_nonneg hfactor_pos.le (hscale_pos V.1).le)
      _ = ENNReal.ofReal ((((1 + 2 * τ : ℝ) ^ d) * ((scale V.1) ^ d))) * volume C := by
            rw [mul_pow]
      _ = ENNReal.ofReal (((1 + 2 * τ : ℝ) ^ d)) *
            (ENNReal.ofReal ((scale V.1) ^ d) * volume C) := by
            rw [ENNReal.ofReal_mul (by positivity : 0 ≤ ((1 + 2 * τ : ℝ) ^ d)), mul_assoc]
      _ = ENNReal.ofReal (((1 + 2 * τ : ℝ) ^ d)) * volume V.1.1 := by
            rw [hvolV]
  have hselected_fin : volume (⋃₀ (Subtype.val '' u)) < ⊤ := by
    refine lt_of_le_of_lt (measure_mono ?_) h𝒰_fin
    intro x hx
    rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
    rcases hU with ⟨V, hV, rfl⟩
    exact mem_sUnion.2 ⟨V.1, V.2, hxU⟩
  have hmeasure :
      volume (⋃₀ 𝒰) ≤ ENNReal.ofReal (((1 + 2 * τ) : ℝ) ^ d) * volume (⋃₀ (Subtype.val '' u)) := by
    haveI : Encodable u := hu_count.toEncodable
    have hsum_u : ∑' V : u, volume V.1.1 = volume (⋃₀ (Subtype.val '' u)) := by
      have hsum_u' : volume (⋃ V : u, V.1.1) = ∑' V : u, volume V.1.1 := by
        exact measure_iUnion hsubtype_disj (fun V ↦ hmember_meas V.1)
      simpa [himage_union] using hsum_u'.symm
    calc
      volume (⋃₀ 𝒰)
          ≤ volume (⋃ V : u,
              ({center V.1} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V.1) • C)) := by
                exact measure_mono hcover_subset
      _ ≤ ∑' V : u,
            volume (({center V.1} : Set (Fin d → ℝ)) + (((1 + 2 * τ) * scale V.1) • C)) := by
              exact measure_iUnion_le _
      _ = ∑' V : u, ENNReal.ofReal (((1 + 2 * τ : ℝ) ^ d)) * volume V.1.1 := by
            refine tsum_congr hmeasure_member
      _ = ENNReal.ofReal (((1 + 2 * τ : ℝ) ^ d)) * ∑' V : u, volume V.1.1 := by
            rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (((1 + 2 * τ) : ℝ) ^ d) * volume (⋃₀ (Subtype.val '' u)) := by
            rw [hsum_u]
  have hscaled_fin :
      ENNReal.ofReal (((1 + 2 * τ) : ℝ) ^ d) * volume (⋃₀ (Subtype.val '' u)) ≠ ⊤ := by
    exact ENNReal.mul_ne_top (by simp) hselected_fin.ne
  -- Proof comment: after the ENNReal estimate is proved, convert back to the real-valued volume.
  have hreal := ENNReal.toReal_mono hscaled_fin hmeasure
  calc
    volume.real (⋃₀ 𝒰) ≤
        (ENNReal.ofReal (((1 + 2 * τ) : ℝ) ^ d) * volume (⋃₀ (Subtype.val '' u))).toReal := hreal
    _ = (ENNReal.ofReal (((1 + 2 * τ) : ℝ) ^ d)).toReal * volume.real (⋃₀ (Subtype.val '' u)) := by
          rw [ENNReal.toReal_mul, Measure.real_def]
    _ = ((1 + 2 * τ) : ℝ) ^ d * volume.real (⋃₀ (Subtype.val '' u)) := by
          rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ ((1 + 2 * τ) : ℝ) ^ d)]

/-- Helper for Exercise 13.1.5: positive union volume forces the common model to be nonempty. -/
private lemma modelNonempty_of_positiveUnionVolume {d : ℕ} {C : Set (Fin d → ℝ)}
    {𝒰 : Set (Set (Fin d → ℝ))} (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰)
    (h𝒰_pos : 0 < volume.real (⋃₀ 𝒰)) : C.Nonempty := by
  have hUnion_nonempty : (⋃₀ 𝒰).Nonempty := by
    -- Proof comment: a zero-volume union would contradict the strict positivity hypothesis.
    by_contra hEmpty
    have hzero : volume.real (⋃₀ 𝒰) = 0 := by
      simp [Set.not_nonempty_iff_eq_empty.mp hEmpty]
    linarith
  rcases hUnion_nonempty with ⟨x, hx⟩
  rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
  rcases hfamily U hU with ⟨center, r, hr, hU_eq⟩
  rw [hU_eq] at hxU
  rcases mem_singleton_add_smul_iff.mp hxU with ⟨c, hc, _⟩
  exact ⟨c, hc⟩

/-- Helper for Exercise 13.1.5: positive union volume forces one actual family member to have
positive Lebesgue volume. -/
private lemma memberWithPositiveVolume_of_positiveUnionVolume {d : ℕ} {C : Set (Fin d → ℝ)}
    {𝒰 : Set (Set (Fin d → ℝ))} (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C)
    (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰) (h𝒰_pos : 0 < volume.real (⋃₀ 𝒰)) :
    ∃ U ∈ 𝒰, 0 < volume.real U := by
  have hUnion_nonempty : (⋃₀ 𝒰).Nonempty := by
    -- Proof comment: the strict positivity hypothesis again rules out the empty union.
    by_contra hEmpty
    have hzero : volume.real (⋃₀ 𝒰) = 0 := by
      simp [Set.not_nonempty_iff_eq_empty.mp hEmpty]
    linarith
  have hC_nonempty : C.Nonempty := modelNonempty_of_positiveUnionVolume hfamily h𝒰_pos
  have hC_pos : 0 < volume.real C :=
    volumeReal_pos_of_open_of_bounded_of_nonempty hC_open hC_bounded hC_nonempty
  rcases hUnion_nonempty with ⟨x, hx⟩
  rcases mem_sUnion.1 hx with ⟨U, hU, hxU⟩
  rcases hfamily U hU with ⟨center, r, hr, hU_eq⟩
  have hvol_copy : 0 < volume.real (({center} : Set (Fin d → ℝ)) + r • C) := by
    -- Proof comment: positive dilates preserve strict positivity because the model itself has
    -- positive volume.
    rw [translatedSmul_volumeReal hC_open.measurableSet center hr]
    exact mul_pos (pow_pos hr _) hC_pos
  exact ⟨U, hU, by simpa [hU_eq] using hvol_copy⟩

/-- Helper for Exercise 13.1.5: the Vitali lower bound for a centrally symmetric common model,
provided the family union has positive volume. -/
theorem disjoint_selection_of_originSymmetric_model
    (d : ℕ) (C : Set (Fin d → ℝ)) (𝒰 : Set (Set (Fin d → ℝ)))
    (hC_open : IsOpen C) (hC_bounded : Bornology.IsBounded C) (hC_convex : Convex ℝ C)
    (hC_symm : IsOriginSymmetric C) (hfamily : IsPositiveHomotheticCopyFamilyOf C 𝒰)
    (h𝒰_fin : volume (⋃₀ 𝒰) < ⊤) (h𝒰_pos : 0 < volume.real (⋃₀ 𝒰)) :
    HasLargeMeasureSelection 𝒰 := by
  intro ε hε
  by_cases hε_lt_one : ε < 1
  · by_cases hd : d = 0
    · subst hd
      obtain ⟨U, hU, hU_pos⟩ :=
        memberWithPositiveVolume_of_positiveUnionVolume hC_open hC_bounded hfamily h𝒰_pos
      have hU_nonempty : U.Nonempty := by
        -- Proof comment: a positive-volume set cannot be empty.
        by_contra hEmpty
        have hzero : volume.real U = 0 := by
          simp [Set.not_nonempty_iff_eq_empty.mp hEmpty]
        linarith
      have hUnion_nonempty : (⋃₀ 𝒰 : Set (Fin 0 → ℝ)).Nonempty := by
        -- Proof comment: the same positivity argument rules out the empty union.
        by_contra hEmpty
        have hzero : volume.real (⋃₀ 𝒰 : Set (Fin 0 → ℝ)) = 0 := by
          simp [Set.not_nonempty_iff_eq_empty.mp hEmpty]
        linarith
      have hU_univ : U = (Set.univ : Set (Fin 0 → ℝ)) := by
        -- Proof comment: every nonempty subset of the singleton `Fin 0 → ℝ` is the whole space.
        ext x
        constructor
        · intro hx
          simp
        · intro hx
          rcases hU_nonempty with ⟨y, hy⟩
          have hxy : x = y := Subsingleton.elim _ _
          simpa [hxy] using hy
      have hUnion_univ : (⋃₀ 𝒰 : Set (Fin 0 → ℝ)) = Set.univ := by
        -- Proof comment: the union is also a nonempty subset of the same singleton space.
        ext x
        constructor
        · intro hx
          simp
        · intro hx
          rcases hUnion_nonempty with ⟨y, hy⟩
          have hxy : x = y := Subsingleton.elim _ _
          simpa [hxy] using hy
      refine ⟨{U}, ?_, ?_, ?_⟩
      · -- Proof comment: the singleton selection is taken from the original family.
        intro V hV
        have hVU : V = U := by simpa using hV
        simpa [hVU] using hU
      · -- Proof comment: a singleton family is pairwise disjoint for the vacuous reason that it
        -- has no distinct members.
        intro V W hV hW hVW
        exfalso
        have hVU : V = U := by simpa using hV
        have hWU : W = U := by simpa using hW
        exact hVW (hVU.trans hWU.symm)
      · -- Proof comment: in dimension `0`, the union and the chosen member are both the whole
        -- singleton space, so strict positivity of `volume.real U` gives the estimate directly.
        have htarget : ((1 - ε) : ℝ) * volume.real U < volume.real U := by
          nlinarith [hε, hU_pos]
        simpa [hU_univ, hUnion_univ] using htarget
    · obtain ⟨τ, hτ_gt, hfactor⟩ := exists_almostThree_enlargementFactor hε hε_lt_one
      have hC_nonempty : C.Nonempty :=
        modelNonempty_of_positiveUnionVolume hfamily h𝒰_pos
      have hC_zero : (0 : Fin d → ℝ) ∈ C :=
        zero_mem_of_nonempty_of_convex_of_originSymmetric hC_convex hC_symm hC_nonempty
      obtain ⟨u, hu_disj, hu_count, hu_cover⟩ :=
        existsCountableDisjointCoveringSubfamily hd hC_open hC_nonempty hfamily h𝒰_fin hτ_gt
      let v : Set (Set (Fin d → ℝ)) := Subtype.val '' u
      have hv_count : v.Countable := hu_count.image Subtype.val
      have hv_disj : v.PairwiseDisjoint id := by
        -- Proof comment: the image family stays pairwise disjoint because the subtype selection
        -- was already pairwise disjoint before forgetting the membership proof.
        intro U hU V hV hUV
        rcases hU with ⟨U', hU', rfl⟩
        rcases hV with ⟨V', hV', rfl⟩
        exact hu_disj hU' hV' (by
          intro hEq
          apply hUV
          simpa using congrArg Subtype.val hEq)
      have hv_meas : ∀ V ∈ v, MeasurableSet V := by
        -- Proof comment: each selected member is still an open positive dilate of `C`.
        intro V hV
        rcases hV with ⟨W, hW, rfl⟩
        rcases hfamily W.1 W.2 with ⟨center, scale, hscale_pos, hW_eq⟩
        have hW_open : IsOpen W.1 := by
          rw [hW_eq, singleton_add]
          exact (Homeomorph.addLeft center).isOpenMap _ (hC_open.smul₀ hscale_pos.ne')
        exact hW_open.measurableSet
      have hv_fin : volume (⋃₀ v) < ⊤ := by
        -- Proof comment: the selected subfamily still lives inside the original family union.
        refine lt_of_le_of_lt (measure_mono ?_) h𝒰_fin
        intro x hx
        rcases mem_sUnion.1 hx with ⟨V, hV, hxV⟩
        rcases hV with ⟨W, hW, rfl⟩
        exact mem_sUnion.2 ⟨W.1, W.2, hxV⟩
      have hscaled :
          volume.real (⋃₀ 𝒰) ≤ ((1 + 2 * τ) : ℝ) ^ d * volume.real (⋃₀ v) :=
        measure_sUnion_le_scaledSelection hd hC_open hC_bounded hC_convex hC_symm hC_zero
          hfamily h𝒰_fin hu_count hu_disj hτ_gt hu_cover
      have hv_nonneg : 0 ≤ volume.real (⋃₀ v) := measureReal_nonneg
      have hcoef_nonneg : 0 ≤ ((1 - ε) / (3 : ℝ) ^ d : ℝ) := by
        exact div_nonneg (sub_nonneg.mpr hε_lt_one.le) (by positivity)
      have hscaled' :
          ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) ≤
            ((((1 - ε) / (3 : ℝ) ^ d) * ((1 + 2 * τ) : ℝ) ^ d) * volume.real (⋃₀ v)) := by
        -- Proof comment: multiply the whole-union estimate by the target coefficient.
        have hmul := mul_le_mul_of_nonneg_left hscaled hcoef_nonneg
        simpa [v, mul_assoc, mul_left_comm, mul_comm] using hmul
      have hfactor_lt_one : (((1 - ε) / (3 : ℝ) ^ d) * ((1 + 2 * τ) : ℝ) ^ d) < 1 := by
        -- Proof comment: the enlargement factor was chosen so that its scaled coefficient falls
        -- strictly below `1`.
        have hden_pos : 0 < 1 - ε := sub_pos.mpr hε_lt_one
        have hpow_pos : 0 < (3 : ℝ) ^ d := by positivity
        have hmul_lt : ((1 + 2 * τ : ℝ) ^ d) * (1 - ε) < (3 : ℝ) ^ d := by
          exact (lt_div_iff₀ hden_pos).mp hfactor
        have hratio : (((1 - ε) * ((1 + 2 * τ : ℝ) ^ d)) / (3 : ℝ) ^ d) < 1 := by
          exact (div_lt_iff₀ hpow_pos).2 (by simpa [mul_comm] using hmul_lt)
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hratio
      have htarget :
          ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) < volume.real (⋃₀ v) := by
        have hv_pos : 0 < volume.real (⋃₀ v) := by
          -- Proof comment: the selected union must still have positive volume because it controls
          -- the strictly positive full union after the fixed enlargement factor.
          by_contra hv_not_pos
          have hv_eq_zero : volume.real (⋃₀ v) = 0 := by
            exact le_antisymm (le_of_not_gt hv_not_pos) hv_nonneg
          have hunion_nonpos : volume.real (⋃₀ 𝒰) ≤ 0 := by
            simpa [hv_eq_zero] using hscaled
          exact (not_le_of_gt h𝒰_pos) hunion_nonpos
        have hstrict :
            ((((1 - ε) / (3 : ℝ) ^ d) * ((1 + 2 * τ) : ℝ) ^ d) * volume.real (⋃₀ v)) <
              1 * volume.real (⋃₀ v) := by
          exact mul_lt_mul_of_pos_right hfactor_lt_one hv_pos
        exact lt_of_le_of_lt hscaled' (by simpa using hstrict)
      obtain ⟨s, hs_subset, hs_disj, hs_sum⟩ :=
        existsFinset_sum_gt_of_lt_volumeReal_sUnion hv_count hv_disj hv_meas hv_fin htarget
      refine ⟨s, ?_, ?_, hs_sum⟩
      · -- Proof comment: every finite selected member comes from the image of the original family.
        intro V hV
        rcases hs_subset (by simpa using hV) with ⟨W, hW, rfl⟩
        exact W.2
      · -- Proof comment: pairwise disjointness is inherited from the finite truncation theorem.
        intro U V hU hV hUV
        exact hs_disj (by simpa using hU) (by simpa using hV) hUV
  · have hε_ge_one : 1 ≤ ε := le_of_not_gt hε_lt_one
    obtain ⟨U, hU, hU_pos⟩ :=
      memberWithPositiveVolume_of_positiveUnionVolume hC_open hC_bounded hfamily h𝒰_pos
    refine ⟨{U}, ?_, ?_, ?_⟩
    · -- Proof comment: the singleton selection is again drawn from the original family.
      intro V hV
      have hVU : V = U := by simpa using hV
      simpa [hVU] using hU
    · -- Proof comment: singleton selections are pairwise disjoint vacuously.
      intro V W hV hW hVW
      exfalso
      have hVU : V = U := by simpa using hV
      have hWU : W = U := by simpa using hW
      exact hVW (hVU.trans hWU.symm)
    · -- Proof comment: once `ε ≥ 1`, the requested lower bound is nonpositive, so any positive
      -- volume member suffices.
      have hcoef_nonpos : ((1 - ε) / (3 : ℝ) ^ d : ℝ) ≤ 0 := by
        refine div_nonpos_of_nonpos_of_nonneg ?_ (by positivity)
        linarith [hε_ge_one]
      have hleft_nonpos :
          ((1 - ε) / (3 : ℝ) ^ d) * volume.real (⋃₀ 𝒰) ≤ 0 := by
        exact mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos measureReal_nonneg
      have hsum_pos : 0 < ({U} : Finset (Set (Fin d → ℝ))).sum (fun V ↦ volume.real V) := by
        simpa using hU_pos
      exact lt_of_le_of_lt hleft_nonpos hsum_pos

/-- Helper for Exercise 13.1.5: the sheared strip used in the counterexample family. -/
private def shearStrip (t : ℝ) : Set (Fin 2 → ℝ) :=
  {p | |p 0| < 1 ∧ |p 1 - t * p 0| < (1 / 10 : ℝ)}

/-- Helper for Exercise 13.1.5: the explicit family of sheared strips indexed by slopes in
`[0, 10]`. -/
private def shearStripFamily : Set (Set (Fin 2 → ℝ)) :=
  Set.range fun t : Set.Icc (0 : ℝ) 10 ↦ shearStrip t.1

/-- Helper for Exercise 13.1.5: a large triangle contained in the union of the strip family. -/
private def shearStripLowerTriangle : Set (Fin 2 → ℝ) :=
  {p | p 0 ∈ Set.Ioo (0 : ℝ) 1 ∧ p 1 ∈ Set.Ioo (0 : ℝ) (10 * p 0)}

/-- Helper for Exercise 13.1.5: a fixed bounding rectangle for the strip union. -/
private def shearStripBoundingRectangle : Set (Fin 2 → ℝ) :=
  {p | |p 0| < 1 ∧ |p 1| < (11 : ℝ)}

/-- Helper for Exercise 13.1.5: coordinate bounds imply boundedness in `Fin 2 → ℝ`. -/
private lemma bounded_of_coordinate_bounds {s : Set (Fin 2 → ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ p ∈ s, ‖p 0‖ ≤ R ∧ ‖p 1‖ ≤ R) :
    Bornology.IsBounded s := by
  -- Proof comment: the sup norm on `Fin 2 → ℝ` is controlled by the two coordinate bounds, so the
  -- whole set lies in a fixed closed ball.
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, ?_⟩
  intro p hp
  have hp0 : ‖p 0‖ ≤ R := (hs p hp).1
  have hp1 : ‖p 1‖ ≤ R := (hs p hp).2
  have hp0' : ‖p 0‖₊ ≤ ⟨R, hR⟩ := by
    exact_mod_cast hp0
  have hp1' : ‖p 1‖₊ ≤ ⟨R, hR⟩ := by
    exact_mod_cast hp1
  have hsup : Finset.univ.sup (fun i : Fin 2 ↦ ‖p i‖₊) ≤ ⟨R, hR⟩ := by
    apply Finset.sup_le
    intro i hi
    fin_cases i
    · simpa using hp0'
    · simpa using hp1'
  have hnorm : ‖p‖ ≤ R := by
    rw [Pi.norm_def]
    exact_mod_cast hsup
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Helper for Exercise 13.1.5: normalize `piFinTwo` image membership to the canonical
two-coordinate point `![q.1, q.2]`. -/
private lemma mem_image_piFinTwo_iff {s : Set (Fin 2 → ℝ)} {q : ℝ × ℝ} :
    q ∈ (MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' s ↔ ![q.1, q.2] ∈ s := by
  constructor
  · intro hq
    rcases hq with ⟨p, hp, hpq⟩
    -- Proof comment: identify the preimage point coordinatewise so the image witness becomes the
    -- canonical vector `![q.1, q.2]`.
    have hp_eq : p = ![q.1, q.2] := by
      ext i
      fin_cases i
      · exact congrArg Prod.fst hpq
      · exact congrArg Prod.snd hpq
    simpa [hp_eq] using hp
  · intro hq
    -- Proof comment: the canonical vector maps back to `q` by the defining formula of
    -- `MeasurableEquiv.piFinTwo`.
    refine ⟨![q.1, q.2], hq, rfl⟩

/-- Helper for Exercise 13.1.5: the strip image in product coordinates is a standard
`regionBetween` set. -/
private lemma image_shearStrip_eq_regionBetween (t : ℝ) :
    (MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' shearStrip t =
      regionBetween (fun x : ℝ ↦ t * x - (1 / 10 : ℝ))
        (fun x : ℝ ↦ t * x + (1 / 10 : ℝ)) (Set.Ioo (-1 : ℝ) 1) := by
  -- Proof comment: after the `piFinTwo` image is normalized to `![q.1, q.2]`, the strip
  -- inequalities and the `regionBetween` inequalities are the same affine bounds.
  ext q
  rw [mem_image_piFinTwo_iff]
  constructor
  · rintro ⟨hq0, hq1⟩
    refine ⟨?_, ?_⟩
    · simpa [abs_lt] using hq0
    · rw [abs_lt] at hq1
      have hlow : -(1 / 10 : ℝ) < q.2 - t * q.1 := by
        simpa using hq1.1
      have hhigh : q.2 - t * q.1 < (1 / 10 : ℝ) := by
        simpa using hq1.2
      rw [Set.mem_Ioo]
      constructor <;> linarith
  · rintro ⟨hq0, hq1⟩
    refine ⟨?_, ?_⟩
    · simpa [abs_lt] using hq0
    · rw [Set.mem_Ioo] at hq1
      rw [abs_lt]
      constructor
      · have : -(1 / 10 : ℝ) < q.2 - t * q.1 := by linarith [hq1.1]
        simpa using this
      · have : q.2 - t * q.1 < (1 / 10 : ℝ) := by linarith [hq1.2]
        simpa using this

/-- Helper for Exercise 13.1.5: `piFinTwo` preserves real-valued volume on measurable sets. -/
private lemma volumeReal_piFinTwo_image_eq {s : Set (Fin 2 → ℝ)} (hs : MeasurableSet s) :
    volume.real ((MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' s) = volume.real s := by
  let e : (Fin 2 → ℝ) ≃ᵐ ℝ × ℝ := MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)
  have hmap : (volume.map e) = (volume : Measure (ℝ × ℝ)) :=
    (MeasureTheory.volume_preserving_piFinTwo (fun _ ↦ ℝ)).map_eq
  -- Proof comment: package the measure-preserving equivalence at the `volume.real` level so the
  -- downstream strip-area computations never reopen the `map` transport.
  calc
    volume.real (e '' s) = (volume.map e).real (e '' s) := by simp [hmap]
    _ = volume.real (e ⁻¹' (e '' s)) := by
      rw [MeasureTheory.map_measureReal_apply e.measurable (e.measurableSet_image.2 hs)]
    _ = volume.real s := by simp

/-- Helper for Exercise 13.1.5: rewrite `regionBetween` volume directly as a real-valued
integral. -/
private lemma volumeReal_regionBetween_eq_integral {f g : ℝ → ℝ} {s : Set ℝ}
    (hf_int : IntegrableOn f s) (hg_int : IntegrableOn g s) (hs : MeasurableSet s)
    (hfg : ∀ x ∈ s, f x ≤ g x) :
    volume.real (regionBetween f g s) = ∫ x in s, (g x - f x) := by
  have hnonneg : 0 ≤ ∫ x in s, (g x - f x) := by
    -- Proof comment: the pointwise order on `s` turns the strip-height integral into a
    -- nonnegative real number, so `ENNReal.toReal_ofReal` applies without further transport.
    exact setIntegral_nonneg hs fun x hx ↦ sub_nonneg.mpr (hfg x hx)
  -- Proof comment: after rewriting ambient product volume once, the existing `regionBetween`
  -- theorem gives the desired real-valued formula directly.
  rw [measureReal_def, MeasureTheory.Measure.volume_eq_prod,
    volume_regionBetween_eq_integral hf_int hg_int hs hfg]
  simpa using ENNReal.toReal_ofReal hnonneg

/-- Helper for Exercise 13.1.5: every strip has the same real volume `2 / 5`. -/
private lemma volumeReal_shearStrip (t : ℝ) :
    volume.real (shearStrip t) = (2 / 5 : ℝ) := by
  have hf_cont : Continuous fun x : ℝ ↦ t * x - (1 / 10 : ℝ) := by continuity
  have hg_cont : Continuous fun x : ℝ ↦ t * x + (1 / 10 : ℝ) := by continuity
  have hstrip_meas : MeasurableSet (shearStrip t) := by
    -- Proof comment: measurability is inherited from the product-coordinate `regionBetween`
    -- description, so the volume-preserving bridge can be applied once and for all.
    refine (MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)).measurableSet_image.1 ?_
    rw [image_shearStrip_eq_regionBetween]
    exact measurableSet_regionBetween hf_cont.measurable hg_cont.measurable measurableSet_Ioo
  have hf_int : IntegrableOn (fun x : ℝ ↦ t * x - (1 / 10 : ℝ)) (Set.Ioo (-1 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    exact hf_cont.intervalIntegrable (-1) 1
  have hg_int : IntegrableOn (fun x : ℝ ↦ t * x + (1 / 10 : ℝ)) (Set.Ioo (-1 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (show (-1 : ℝ) ≤ 1 by norm_num)]
    exact hg_cont.intervalIntegrable (-1) 1
  calc
    volume.real (shearStrip t)
        = volume.real ((MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' shearStrip t) := by
            symm
            exact volumeReal_piFinTwo_image_eq hstrip_meas
    _ = volume.real
          (regionBetween (fun x : ℝ ↦ t * x - (1 / 10 : ℝ))
            (fun x : ℝ ↦ t * x + (1 / 10 : ℝ)) (Set.Ioo (-1 : ℝ) 1)) := by
          rw [image_shearStrip_eq_regionBetween]
    _ = ∫ x in Set.Ioo (-1 : ℝ) 1, ((t * x + (1 / 10 : ℝ)) - (t * x - (1 / 10 : ℝ))) := by
          apply volumeReal_regionBetween_eq_integral hf_int hg_int measurableSet_Ioo
          intro x hx
          linarith
    _ = ∫ _ in Set.Ioo (-1 : ℝ) 1, (1 / 5 : ℝ) := by
          congr with x
          ring
    _ = volume.real (Set.Ioo (-1 : ℝ) 1) * (1 / 5 : ℝ) := by
          rw [setIntegral_const, smul_eq_mul]
    _ = (2 / 5 : ℝ) := by
          norm_num [measureReal_def, Real.volume_Ioo]

/-- Helper for Exercise 13.1.5: the lower triangle image is the expected `regionBetween` set. -/
private lemma image_shearStripLowerTriangle_eq_regionBetween :
    (MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' shearStripLowerTriangle =
      regionBetween (fun _ : ℝ ↦ (0 : ℝ)) (fun x : ℝ ↦ (10 : ℝ) * x) (Set.Ioo (0 : ℝ) 1) := by
  -- Proof comment: after the same `piFinTwo` normalization, the triangle inequalities already
  -- match the `regionBetween` normal form verbatim.
  ext q
  rw [mem_image_piFinTwo_iff]
  rfl

/-- Helper for Exercise 13.1.5: the lower triangle has real volume `5`. -/
private lemma volumeReal_shearStripLowerTriangle :
    volume.real shearStripLowerTriangle = (5 : ℝ) := by
  have htriangle_meas : MeasurableSet shearStripLowerTriangle := by
    -- Proof comment: reuse the same image-measurability bridge so the triangle area proof stays in
    -- product coordinates after one rewrite.
    refine (MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)).measurableSet_image.1 ?_
    rw [image_shearStripLowerTriangle_eq_regionBetween]
    exact measurableSet_regionBetween measurable_const
      ((by continuity : Continuous fun x : ℝ ↦ (10 : ℝ) * x).measurable) measurableSet_Ioo
  have hg_cont : Continuous fun x : ℝ ↦ (10 : ℝ) * x := by continuity
  have hf_int : IntegrableOn (fun _ : ℝ ↦ (0 : ℝ)) (Set.Ioo (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact continuous_const.intervalIntegrable 0 1
  have hg_int : IntegrableOn (fun x : ℝ ↦ (10 : ℝ) * x) (Set.Ioo (0 : ℝ) 1) := by
    rw [← intervalIntegrable_iff_integrableOn_Ioo_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
    exact hg_cont.intervalIntegrable 0 1
  calc
    volume.real shearStripLowerTriangle
        = volume.real ((MeasurableEquiv.piFinTwo (fun _ ↦ ℝ)) '' shearStripLowerTriangle) := by
            symm
            exact volumeReal_piFinTwo_image_eq htriangle_meas
    _ = volume.real
          (regionBetween (fun _ : ℝ ↦ (0 : ℝ)) (fun x : ℝ ↦ (10 : ℝ) * x)
            (Set.Ioo (0 : ℝ) 1)) := by
          rw [image_shearStripLowerTriangle_eq_regionBetween]
    _ = ∫ x in Set.Ioo (0 : ℝ) 1, ((10 : ℝ) * x - 0) := by
          apply volumeReal_regionBetween_eq_integral hf_int hg_int measurableSet_Ioo
          intro x hx
          nlinarith [hx.1.le]
    _ = ∫ x in Set.Ioo (0 : ℝ) 1, (10 : ℝ) * x := by simp
    _ = ∫ x in (0 : ℝ)..1, (10 : ℝ) * x := by
          symm
          rw [intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
            integral_Ioc_eq_integral_Ioo]
    _ = (5 : ℝ) := by
          rw [intervalIntegral.integral_const_mul, integral_id]
          norm_num

/-- Helper for Exercise 13.1.5: each strip is open, bounded, and convex. -/
private lemma isOpenBoundedConvexSet_shearStrip {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 10) :
    IsOpenBoundedConvexSet (shearStrip t) := by
  rcases ht with ⟨ht_nonneg, ht_le_ten⟩
  let proj0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0
  let shear : (Fin 2 → ℝ) →ₗ[ℝ] ℝ := (LinearMap.proj 1 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) - t • proj0
  have hstrip_repr :
      shearStrip t =
        (fun p : Fin 2 → ℝ ↦ p 0) ⁻¹' Set.Ioo (-1 : ℝ) 1 ∩
          (fun p : Fin 2 → ℝ ↦ p 1 - t * p 0) ⁻¹' Set.Ioo (-(1 / 10 : ℝ)) (1 / 10 : ℝ) := by
    ext p
    simp [shearStrip, abs_lt]
  have hopen0 : IsOpen ((fun p : Fin 2 → ℝ ↦ p 0) ⁻¹' Set.Ioo (-1 : ℝ) 1) := by
    exact (show Continuous (fun p : Fin 2 → ℝ ↦ p 0) from continuous_apply 0).isOpen_preimage
      (Set.Ioo (-1 : ℝ) 1) isOpen_Ioo
  have hopen1 :
      IsOpen ((fun p : Fin 2 → ℝ ↦ p 1 - t * p 0) ⁻¹' Set.Ioo (-(1 / 10 : ℝ)) (1 / 10 : ℝ)) := by
    have hcont : Continuous fun p : Fin 2 → ℝ ↦ p 1 - t * p 0 := by continuity
    exact hcont.isOpen_preimage (Set.Ioo (-(1 / 10 : ℝ)) (1 / 10 : ℝ)) isOpen_Ioo
  have hconv0 : Convex ℝ ((fun p : Fin 2 → ℝ ↦ p 0) ⁻¹' Set.Ioo (-1 : ℝ) 1) := by
    simpa [proj0] using (convex_Ioo (-1 : ℝ) 1).linear_preimage proj0
  have hconv1 :
      Convex ℝ ((fun p : Fin 2 → ℝ ↦ p 1 - t * p 0) ⁻¹' Set.Ioo (-(1 / 10 : ℝ)) (1 / 10 : ℝ)) := by
    simpa [shear, proj0] using
      (convex_Ioo (-(1 / 10 : ℝ)) (1 / 10 : ℝ)).linear_preimage shear
  refine ⟨?_, ?_, ?_⟩
  · -- Proof comment: the strip is the intersection of two open slabs cut out by continuous
    -- coordinate functionals.
    rw [hstrip_repr]
    exact hopen0.inter hopen1
  · -- Proof comment: the slope bound `0 ≤ t ≤ 10` gives uniform coordinate bounds, hence
    -- boundedness in the sup norm on `Fin 2 → ℝ`.
    refine bounded_of_coordinate_bounds (show (0 : ℝ) ≤ 11 by norm_num) ?_
    intro p hp
    rcases hp with ⟨hp0, hp1⟩
    have hp0_le : |p 0| ≤ 11 := by nlinarith [hp0]
    have hmul : |t * p 0| ≤ 10 := by
      calc
        |t * p 0| = |t| * |p 0| := by rw [abs_mul]
        _ = t * |p 0| := by rw [abs_of_nonneg ht_nonneg]
        _ ≤ t := by nlinarith [hp0]
        _ ≤ 10 := by exact ht_le_ten
    have hsum : |p 1 - t * p 0| + |t * p 0| < 11 := by
      nlinarith
    have hdecomp : p 1 = (p 1 - t * p 0) + t * p 0 := by ring
    have hp1_abs : |p 1| ≤ |p 1 - t * p 0| + |t * p 0| := by
      have habs := abs_add_le (p 1 - t * p 0) (t * p 0)
      rw [← hdecomp] at habs
      exact habs
    have hp1_le : |p 1| ≤ 11 := by
      exact le_of_lt (lt_of_le_of_lt hp1_abs hsum)
    exact ⟨by simpa [Real.norm_eq_abs] using hp0_le, by simpa [Real.norm_eq_abs] using hp1_le⟩
  · -- Proof comment: convexity is inherited from the two interval preimages under linear maps.
    rw [hstrip_repr]
    exact hconv0.inter hconv1

/-- Helper for Exercise 13.1.5: every strip in the family contains the origin. -/
private lemma zero_mem_shearStripFamily_member {U : Set (Fin 2 → ℝ)} (hU : U ∈ shearStripFamily) :
    (0 : Fin 2 → ℝ) ∈ U := by
  -- Proof comment: the origin satisfies both strip inequalities for every slope.
  rcases hU with ⟨t, -, rfl⟩
  simp [shearStrip]

/-- Helper for Exercise 13.1.5: the lower triangle lies inside the strip union. -/
private lemma shearStripLowerTriangle_subset_sUnion_family :
    shearStripLowerTriangle ⊆ ⋃₀ shearStripFamily := by
  intro p hp
  rcases hp with ⟨hp0, hp1⟩
  have hp0_pos : 0 < p 0 := hp0.1
  have hp0_ne : p 0 ≠ 0 := ne_of_gt hp0_pos
  let t : Set.Icc (0 : ℝ) 10 :=
    ⟨p 1 / p 0, by
      constructor
      · exact div_nonneg hp1.1.le hp0.1.le
      · exact le_of_lt ((div_lt_iff₀ hp0_pos).2 (by simpa using hp1.2))⟩
  refine mem_sUnion.2 ⟨shearStrip t.1, ⟨t, rfl⟩, ?_⟩
  constructor
  · have hp0_abs : |p 0| < (1 : ℝ) := by
      rw [abs_of_pos hp0_pos]
      exact hp0.2
    simpa using hp0_abs
  · have hflat : p 1 - t.1 * p 0 = 0 := by
      dsimp [t]
      field_simp [hp0_ne]
      ring_nf
    simp [hflat]

/-- Helper for Exercise 13.1.5: the strip union stays inside the fixed rectangle. -/
private lemma sUnion_shearStripFamily_subset_boundingRectangle :
    ⋃₀ shearStripFamily ⊆ shearStripBoundingRectangle := by
  intro p hp
  rcases mem_sUnion.1 hp with ⟨U, hU, hpU⟩
  rcases hU with ⟨t, ht, rfl⟩
  rcases hpU with ⟨hp0, hp1⟩
  constructor
  · exact hp0
  · have ht_nonneg : 0 ≤ t.1 := t.2.1
    have hmul : |t.1 * p 0| ≤ 10 := by
      calc
        |t.1 * p 0| = |t.1| * |p 0| := by rw [abs_mul]
        _ = t.1 * |p 0| := by rw [abs_of_nonneg ht_nonneg]
        _ ≤ t.1 := by nlinarith [hp0]
        _ ≤ 10 := by nlinarith [t.2.2]
    have hsum : |p 1 - t.1 * p 0| + |t.1 * p 0| < 11 := by
      nlinarith
    have hdecomp : p 1 = (p 1 - t.1 * p 0) + t.1 * p 0 := by ring
    have habs : |p 1| ≤ |p 1 - t.1 * p 0| + |t.1 * p 0| := by
      have habs' := abs_add_le (p 1 - t.1 * p 0) (t.1 * p 0)
      rw [← hdecomp] at habs'
      exact habs'
    calc
      |p 1| ≤ |p 1 - t.1 * p 0| + |t.1 * p 0| := habs
      _ < 11 := hsum

/-- Helper for Exercise 13.1.5: package the concrete strip-family facts needed in the final
counterexample theorem. -/
private lemma shearStripFamilySpec :
    IsOpenBoundedConvexFamily shearStripFamily ∧
      (∀ U ∈ shearStripFamily, (0 : Fin 2 → ℝ) ∈ U) ∧
      (5 : ℝ) ≤ volume.real (⋃₀ shearStripFamily) ∧
      HasFiniteUnionMeasure shearStripFamily := by
  have hrect_bounded : Bornology.IsBounded shearStripBoundingRectangle := by
    -- Proof comment: the bounding rectangle has uniform coordinate bounds `1` and `11`, so it has
    -- finite Lebesgue measure.
    refine bounded_of_coordinate_bounds (show (0 : ℝ) ≤ 11 by norm_num) ?_
    intro p hp
    exact ⟨by
      simpa [Real.norm_eq_abs] using (show |p 0| ≤ 11 by nlinarith [hp.1]), by
      simpa [Real.norm_eq_abs] using (show |p 1| ≤ 11 by nlinarith [hp.2])⟩
  have hfinite :
      HasFiniteUnionMeasure shearStripFamily := by
    refine lt_of_le_of_lt (measure_mono sUnion_shearStripFamily_subset_boundingRectangle)
      hrect_bounded.measure_lt_top
  have htriangle_le :
      volume.real shearStripLowerTriangle ≤ volume.real (⋃₀ shearStripFamily) := by
    exact measureReal_mono shearStripLowerTriangle_subset_sUnion_family hfinite.ne
  refine ⟨?_, (fun U hU ↦ zero_mem_shearStripFamily_member hU), ?_, hfinite⟩
  · -- Proof comment: each member is one of the explicitly verified strips `shearStrip t`.
    intro U hU
    rcases hU with ⟨t, ht, rfl⟩
    exact isOpenBoundedConvexSet_shearStrip t.2
  · -- Proof comment: the lower triangle sits inside the strip union, so its area gives a uniform
    -- lower bound for the whole union volume.
    simpa [volumeReal_shearStripLowerTriangle] using htriangle_le

/-- Helper for Exercise 13.1.5: any pairwise disjoint finite strip subfamily has total real volume
at most one strip volume. -/
private lemma sum_volumeReal_le_of_pairwiseDisjoint_shearStripSubfamily
    (s : Finset (Set (Fin 2 → ℝ))) (hs_subset : (↑s : Set (Set (Fin 2 → ℝ))) ⊆ shearStripFamily)
    (hs_disj : (↑s : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id) :
    s.sum (fun U ↦ volume.real U) ≤ (2 / 5 : ℝ) := by
  classical
  by_cases hs_empty : s = ∅
  · -- Proof comment: the empty case is immediate.
    simp [hs_empty]
    norm_num
  · rcases Finset.nonempty_iff_ne_empty.mpr hs_empty with ⟨U₀, hU₀⟩
    have hall : ∀ U ∈ s, U = U₀ := by
      -- Proof comment: every family member contains the origin, so pairwise disjointness forces a
      -- nonempty finite subfamily to collapse to one set.
      intro U hU
      by_cases hEq : U = U₀
      · exact hEq
      · have hdisj : Disjoint U U₀ :=
          hs_disj (by simpa using hU) (by simpa using hU₀) hEq
        have hzeroU : (0 : Fin 2 → ℝ) ∈ U :=
          zero_mem_shearStripFamily_member (hs_subset (by simpa using hU))
        have hzeroU₀ : (0 : Fin 2 → ℝ) ∈ U₀ :=
          zero_mem_shearStripFamily_member (hs_subset (by simpa using hU₀))
        exact False.elim ((Set.disjoint_left.mp hdisj) hzeroU hzeroU₀)
    have hs_singleton : s = {U₀} := by
      exact Finset.eq_singleton_iff_unique_mem.2 ⟨hU₀, hall⟩
    calc
      s.sum (fun U ↦ volume.real U) =
          ({U₀} : Finset (Set (Fin 2 → ℝ))).sum (fun U ↦ volume.real U) := by
        rw [hs_singleton]
      _ = volume.real U₀ := by simp
      _ = (2 / 5 : ℝ) := by
        rcases hs_subset (by simpa using hU₀) with ⟨t, ht, rfl⟩
        simpa using volumeReal_shearStrip t.1
    norm_num

/-- Helper for Exercise 13.1.5: a positive copy of the horizontal strip is exactly a translated
axis-aligned rectangle. -/
private lemma mem_translate_smul_shearStrip_zero_iff {a p : Fin 2 → ℝ} {r : ℝ} (hr : 0 < r) :
    p ∈ ({a} : Set (Fin 2 → ℝ)) + r • shearStrip 0 ↔
      |p 0 - a 0| < r ∧ |p 1 - a 1| < r / 10 := by
  constructor
  · intro hp
    rcases mem_singleton_add_smul_iff.mp hp with ⟨c, hc, hp_eq⟩
    have hc0 : |c 0| < 1 := by simpa [shearStrip] using hc.1
    have hc1 : |c 1| < (1 / 10 : ℝ) := by simpa [shearStrip] using hc.2
    have hp0_eq : p 0 - a 0 = r * c 0 := by
      have hcoord := congrArg (fun q : Fin 2 → ℝ ↦ q 0) hp_eq
      simpa [Pi.smul_apply] using sub_eq_iff_eq_add'.2 hcoord
    have hp1_eq : p 1 - a 1 = r * c 1 := by
      have hcoord := congrArg (fun q : Fin 2 → ℝ ↦ q 1) hp_eq
      simpa [Pi.smul_apply] using sub_eq_iff_eq_add'.2 hcoord
    constructor
    · -- Proof comment: the first coordinate of a translated horizontal strip is controlled by the
      -- positive scaling factor `r`.
      have hmul : r * |c 0| < r * 1 := mul_lt_mul_of_pos_left hc0 hr
      simpa [hp0_eq, abs_mul, abs_of_pos hr, Pi.smul_apply] using hmul
    · -- Proof comment: the second coordinate bound scales in the same way, with the fixed strip
      -- thickness `1 / 10`.
      have hmul : r * |c 1| < r * (1 / 10 : ℝ) := mul_lt_mul_of_pos_left hc1 hr
      simpa [hp1_eq, abs_mul, abs_of_pos hr, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]
        using hmul
  · rintro ⟨hp0, hp1⟩
    let c : Fin 2 → ℝ := fun i ↦ (p i - a i) / r
    have hc0 : |c 0| < 1 := by
      have hdiv : |p 0 - a 0| / r < 1 := by
        exact (div_lt_iff₀ hr).2 (by simpa [one_mul] using hp0)
      simpa [c, abs_div, abs_of_pos hr] using hdiv
    have hc1 : |c 1| < (1 / 10 : ℝ) := by
      have hdiv : |p 1 - a 1| / r < (1 / 10 : ℝ) := by
        exact (div_lt_iff₀ hr).2 (by
          simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hp1)
      simpa [c, abs_div, abs_of_pos hr] using hdiv
    refine mem_singleton_add_smul_iff.mpr ⟨c, by simpa [shearStrip] using And.intro hc0 hc1, ?_⟩
    ext i
    calc
      p i = a i + (p i - a i) := by ring
      _ = a i + r * ((p i - a i) / r) := by
            field_simp [hr.ne']
      _ = a i + r * c i := by simp [c]
      _ = (a + r • c) i := by simp [Pi.smul_apply]

/-- Helper for Exercise 13.1.5: the horizontal strip `shearStrip 0` cannot be a positive
homothetic model for the slanted strip `shearStrip 1`. -/
private lemma shearStrip_zero_not_positiveHomotheticCopyOf_one :
    ¬ IsPositiveHomotheticCopyOf (shearStrip 0) (shearStrip 1) := by
  intro hcopy
  rcases hcopy with ⟨a, r, hr, hcopy_eq⟩
  let q0 : Fin 2 → ℝ := ![0, 0]
  let q1 : Fin 2 → ℝ := ![(1 / 2 : ℝ), (1 / 2 : ℝ)]
  let q2 : Fin 2 → ℝ := ![(1 / 2 : ℝ), (0 : ℝ)]
  have hq0_mem : q0 ∈ shearStrip 1 := by
    simp [q0, shearStrip]
  have hq1_mem : q1 ∈ shearStrip 1 := by
    norm_num [q1, shearStrip]
  have hq0_rect : |q0 0 - a 0| < r ∧ |q0 1 - a 1| < r / 10 := by
    rw [hcopy_eq] at hq0_mem
    exact mem_translate_smul_shearStrip_zero_iff hr |>.mp hq0_mem
  have hq1_rect : |q1 0 - a 0| < r ∧ |q1 1 - a 1| < r / 10 := by
    rw [hcopy_eq] at hq1_mem
    exact mem_translate_smul_shearStrip_zero_iff hr |>.mp hq1_mem
  have hq2_rect : |q2 0 - a 0| < r ∧ |q2 1 - a 1| < r / 10 := by
    -- Proof comment: the translated scaled horizontal strip is a rectangle, so combining the
    -- horizontal bound from `q1` and the vertical bound from `q0` puts `q2` inside it.
    constructor
    · simpa [q2, q1] using hq1_rect.1
    · simpa [q2, q0] using hq0_rect.2
  have hq2_mem : q2 ∈ shearStrip 1 := by
    rw [hcopy_eq]
    exact mem_translate_smul_shearStrip_zero_iff hr |>.mpr hq2_rect
  have hq2_not_mem : q2 ∉ shearStrip 1 := by
    norm_num [q2, shearStrip]
  exact hq2_not_mem hq2_mem

/-- Helper for Exercise 13.1.5: two members that share a common homothetic model are homothetic to
each other. -/
private lemma positiveHomotheticCopyOf_of_commonModelCopies {C U V : Set (Fin 2 → ℝ)}
    (hU : IsPositiveHomotheticCopyOf C U) (hV : IsPositiveHomotheticCopyOf C V) :
    IsPositiveHomotheticCopyOf U V := by
  rcases hU with ⟨x, r, hr, rfl⟩
  rcases hV with ⟨y, s, hs, rfl⟩
  refine ⟨y - (s / r) • x, s / r, div_pos hs hr, ?_⟩
  ext p
  constructor
  · intro hp
    rcases mem_singleton_add_smul_iff.mp hp with ⟨c, hc, hp_eq⟩
    refine mem_singleton_add_smul_iff.mpr ⟨x + r • c, ?_, ?_⟩
    · exact mem_singleton_add_smul_iff.mpr ⟨c, hc, rfl⟩
    · -- Proof comment: choose the corresponding point of `U`, then the two affine descriptions
      -- differ only by a one-line scalar-distribution identity.
      calc
        p = y + s • c := hp_eq
        _ = (y - (s / r) • x) + (s / r) • (x + r • c) := by
              ext i
              simp [Pi.smul_apply]
              field_simp [hr.ne']
              ring
  · intro hp
    rcases mem_singleton_add_smul_iff.mp hp with ⟨u, hu, hp_eq⟩
    rcases mem_singleton_add_smul_iff.mp hu with ⟨c, hc, hu_eq⟩
    refine mem_singleton_add_smul_iff.mpr ⟨c, hc, ?_⟩
    calc
      p = (y - (s / r) • x) + (s / r) • u := hp_eq
      _ = (y - (s / r) • x) + (s / r) • (x + r • c) := by rw [hu_eq]
      _ = y + s • c := by
            ext i
            simp [Pi.smul_apply]
            field_simp [hr.ne']
            ring

/-
The printed claim in the first sentence of Exercise 13.1.5 is false for arbitrary convex common
models, so the source-facing entry `exercise_13_1_5` records that printed proposition as a `Prop`
rather than asserting it as a theorem. The helper theorem
`disjoint_selection_of_originSymmetric_model` above keeps the mathematically valid
origin-symmetric variant available for later proof work. The companion theorem
`nonsimilar_counterexample_to_large_selection` below records the source's second sentence, and
`simplex_common_model_counterexample_to_large_selection` remains as an additional diagnostic
showing that the printed first sentence already fails for a common-model family.
-/

/-- Source-facing proposition for Exercise 13.1.5: the first printed sentence says that if `C` is
open, bounded, and convex,
and `𝒰` consists of positive homothetic copies of `C` whose union has finite Lebesgue measure,
then `𝒰` contains a finite pairwise disjoint subfamily whose total measure is larger than
`((1 - ε) / 3^d) * λ(W)` for every `ε > 0`. This declaration records that printed claim
source-facingly as a `Prop`; the counterexample requested by the second sentence appears below as
the companion theorem `nonsimilar_counterexample_to_large_selection`. -/
def exercise_13_1_5 : Prop :=
    ∀ (d : ℕ) (C : Set (Fin d → ℝ)) (𝒰 : Set (Set (Fin d → ℝ))),
      IsOpenBoundedConvexSet C →
      IsPositiveHomotheticCopyFamilyOf C 𝒰 →
      HasFiniteUnionMeasure 𝒰 →
      HasLargeMeasureSelection 𝒰

/-- Companion specification for `exercise_13_1_5`: this proposition is exactly the printed first
sentence of the exercise, expressed as a source-facing proposition. -/
theorem exercise_13_1_5_iff :
    exercise_13_1_5 ↔
      ∀ (d : ℕ) (C : Set (Fin d → ℝ)) (𝒰 : Set (Set (Fin d → ℝ))),
        IsOpenBoundedConvexSet C →
        IsPositiveHomotheticCopyFamilyOf C 𝒰 →
        HasFiniteUnionMeasure 𝒰 →
        HasLargeMeasureSelection 𝒰 := by
  -- Proof comment: `exercise_13_1_5` was defined as exactly this source-facing proposition.
  rfl

/-- Counterexample companion to `exercise_13_1_5`: there exists a family of open, bounded, convex
subsets of `Fin 2 → ℝ` whose union has finite Lebesgue measure, for which the large-selection
conclusion fails, and which contains two members that are not positive homothetic copies of each
other. This records the source's second sentence that the similarity hypothesis on `𝒰` is
essential. -/
theorem nonsimilar_counterexample_to_large_selection :
    ∃ 𝒰 : Set (Set (Fin 2 → ℝ)),
      IsOpenBoundedConvexFamily 𝒰 ∧
      HasFiniteUnionMeasure 𝒰 ∧
      ¬ HasLargeMeasureSelection 𝒰 ∧
      ∃ U ∈ 𝒰, ∃ V ∈ 𝒰, ¬ IsPositiveHomotheticCopyOf U V := by
  rcases shearStripFamilySpec with ⟨hfamily_open, _, hunion_lower, hfamily_fin⟩
  refine ⟨shearStripFamily, hfamily_open, hfamily_fin, ?_, ?_⟩
  · -- Proof comment: the explicit strip family defeats the large-selection conclusion because any
    -- pairwise disjoint finite subfamily has total volume at most one strip.
    intro hlarge
    rcases hlarge (1 / 5 : ℝ) (by norm_num) with ⟨s, hs_subset, hs_disj, hs_large⟩
    have hs_pairwise : (↑s : Set (Set (Fin 2 → ℝ))).PairwiseDisjoint id := by
      intro U hU V hV hUV
      exact hs_disj hU hV hUV
    have hs_upper :
        s.sum (fun U ↦ volume.real U) ≤ (2 / 5 : ℝ) :=
      sum_volumeReal_le_of_pairwiseDisjoint_shearStripSubfamily s hs_subset hs_pairwise
    have hthreshold_ge : (4 / 9 : ℝ) ≤
        ((1 - (1 / 5 : ℝ)) / (3 : ℝ) ^ 2) * volume.real (⋃₀ shearStripFamily) := by
      have hmul := mul_le_mul_of_nonneg_left hunion_lower (by norm_num : 0 ≤ (4 / 45 : ℝ))
      nlinarith
    have hthreshold_gt : (2 / 5 : ℝ) <
        ((1 - (1 / 5 : ℝ)) / (3 : ℝ) ^ 2) * volume.real (⋃₀ shearStripFamily) := by
      linarith
    have hs_lower : (2 / 5 : ℝ) < s.sum (fun U ↦ volume.real U) :=
      lt_trans hthreshold_gt hs_large
    exact (not_lt_of_ge hs_upper) hs_lower
  · -- Proof comment: the horizontal strip and a slanted strip both lie in the family, but the
    -- geometric obstruction lemma shows they are not positive homothetic copies of one another.
    refine ⟨shearStrip 0, ?_, shearStrip 1, ?_, shearStrip_zero_not_positiveHomotheticCopyOf_one⟩
    · refine ⟨⟨0, by constructor <;> norm_num⟩, rfl⟩
    · refine ⟨⟨1, by constructor <;> norm_num⟩, rfl⟩

/- Diagnostic companion to `exercise_13_1_5`: the remaining theorem below exhibits a
five-dimensional common-model counterexample based on the open simplex. -/
/-- Helper for Exercise 13.1.5: coordinatewise bounds in `Fin d → ℝ` imply boundedness in the
sup norm. -/
private lemma bounded_of_coordinate_bounds_pi {d : ℕ} {s : Set (Fin d → ℝ)} {R : ℝ}
    (hR : 0 ≤ R) (hs : ∀ p ∈ s, ∀ i, ‖p i‖ ≤ R) :
    Bornology.IsBounded s := by
  -- Proof comment: in the finite product norm, the norm is the maximum of the coordinate norms.
  refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨R, ?_⟩
  intro p hp
  have hsup : Finset.univ.sup (fun i : Fin d ↦ ‖p i‖₊) ≤ ⟨R, hR⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast hs p hp i
  have hnorm : ‖p‖ ≤ R := by
    rw [Pi.norm_def]
    exact_mod_cast hsup
  simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm

/-- Helper for Exercise 13.1.5: the finite coordinate sum is measurable on `ι → ℝ`. -/
private theorem prefixSum_measurable_fintype (ι : Type*) [Fintype ι] :
    Measurable (fun z : ι → ℝ ↦ ∑ i, z i) := by
  -- Proof comment: a finite sum of measurable coordinate projections is measurable.
  refine Finset.measurable_sum Finset.univ ?_
  intro i hi
  exact measurable_pi_apply i

/-- Helper for Exercise 13.1.5: the nonnegative simplex sublevel is measurable on every finite
function space. -/
private theorem positiveSimplex_measurableSet_fintype (ι : Type*) [Fintype ι] (a : ℝ) :
    MeasurableSet {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
  have hnonneg : MeasurableSet {z : ι → ℝ | ∀ i, 0 ≤ z i} := by
    rw [show {z : ι → ℝ | ∀ i, 0 ≤ z i} = ⋂ i, {z : ι → ℝ | 0 ≤ z i} by
      ext z
      simp]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i measurableSet_Ici
  have hsum : MeasurableSet {z : ι → ℝ | ∑ i, z i ≤ a} := by
    exact (prefixSum_measurable_fintype ι) measurableSet_Iic
  -- Proof comment: the simplex is an intersection of the nonnegative orthant with a sum sublevel.
  simpa [Set.setOf_and] using hnonneg.inter hsum

/-- Helper for Exercise 13.1.5: the positive simplex in `Fin m → ℝ` is measurable. -/
private theorem positiveSimplex_measurableSet (m : ℕ) (a : ℝ) :
    MeasurableSet {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
  simpa using positiveSimplex_measurableSet_fintype (Fin m) a

/-- Helper for Exercise 13.1.5: the sum of the indicator vector of a finite subset of `Fin m`
equals the subset cardinality. -/
private theorem indicatorFinsetOne_sum (m : ℕ) (s : Finset (Fin m)) :
    ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) = s.card := by
  -- Proof comment: summing the indicator over all coordinates just counts the marked coordinates.
  rw [Finset.sum_ite_mem_eq]
  simp

/-- Helper for Exercise 13.1.5: translating by the indicator vector of `s` identifies the simplex
intersection with the coordinate lower bounds `1 ≤ z i` as a smaller-threshold simplex. -/
private theorem positiveSimplex_shift_preimage
    (m : ℕ) (s : Finset (Fin m)) (t : ℝ) :
    let simplex : ℝ → Set (Fin m → ℝ) :=
      fun a ↦ {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
    (fun z : Fin m → ℝ ↦ z + fun i ↦ if i ∈ s then 1 else 0) ⁻¹'
        (simplex t ∩ ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i}) =
      simplex (t - (s.card : ℝ)) := by
  dsimp
  ext z
  constructor
  · intro hz
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hz ⊢
    rcases hz with ⟨hz_simplex, hz_lower⟩
    constructor
    · intro i
      by_cases hi : i ∈ s
      · have hcoord : 1 ≤ z i + 1 := by
          simpa [hi] using hz_lower i hi
        linarith
      · simpa [hi] using hz_simplex.1 i
    · have hsum_le : ∑ i, (z i + if i ∈ s then 1 else 0) ≤ t := hz_simplex.2
      have hsum_split :
          ∑ i, (z i + if i ∈ s then 1 else 0) =
            ∑ i, z i + ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) := by
        simp [Finset.sum_add_distrib]
      rw [hsum_split, indicatorFinsetOne_sum] at hsum_le
      linarith
  · intro hz
    simp only [Set.mem_preimage, Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter] at hz ⊢
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    constructor
    · constructor
      · intro i
        by_cases hi : i ∈ s
        · have hz_i : 0 ≤ z i := hz_nonneg i
          have : 0 ≤ z i + 1 := by linarith
          simpa [hi] using this
        · simpa [hi] using hz_nonneg i
      · have hsum_split :
            ∑ i, (z i + if i ∈ s then 1 else 0) =
              ∑ i, z i + ∑ i : Fin m, (if i ∈ s then (1 : ℝ) else 0) := by
          simp [Finset.sum_add_distrib]
        rw [hsum_split, indicatorFinsetOne_sum]
        linarith
    · intro i hi
      have hz_i : 0 ≤ z i := hz_nonneg i
      have : 1 ≤ z i + 1 := by linarith
      simpa [hi] using this

/-- Helper for Exercise 13.1.5: the translated simplex intersection has the same real volume as
the smaller-threshold simplex obtained after subtracting the indicator shift. -/
private theorem positiveSimplexShift_real
    (m : ℕ) (s : Finset (Fin m)) (t : ℝ) :
    volume.real
        ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
          ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i}) =
      volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t - (s.card : ℝ)} := by
  -- Proof comment: translation preserves Lebesgue measure, and the preimage is the smaller
  -- simplex from the previous lemma.
  rw [measureReal_def]
  rw [← measure_preimage_add_right
    (volume : Measure (Fin m → ℝ))
    (fun i : Fin m ↦ if i ∈ s then 1 else 0)
    ({z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t} ∩
      ⋂ i ∈ s, {z : Fin m → ℝ | 1 ≤ z i})]
  rw [positiveSimplex_shift_preimage]
  rw [measureReal_def]

/-- Helper for Exercise 13.1.5: a positive-simplex sublevel with negative threshold is empty, so
its real volume vanishes. -/
private theorem positiveSimplexReal_zero_of_lt_zero
    (m : ℕ) (a : ℝ) (ha : a < 0) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = 0 := by
  have hEmpty :
      {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = (∅ : Set (Fin m → ℝ)) := by
    ext z
    constructor
    · intro hz
      rcases hz with ⟨hz_nonneg, hz_sum⟩
      have hsum_nonneg : 0 ≤ ∑ i, z i := by
        refine Finset.sum_nonneg ?_
        intro i hi
        exact hz_nonneg i
      linarith
    · simp
  rw [hEmpty]
  simp

/-- Helper for Exercise 13.1.5: splitting off coordinate `0` with `piFinSuccAbove` rewrites
positive-simplex membership into a head/tail condition. -/
private theorem positiveSimplex_piFinSuccAbove_symm_mem_iff
    (m : ℕ) (a x : ℝ) (y : Fin m → ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm (x, y) ∈
      {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) ↔
      0 ≤ x ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x := by
  -- Proof comment: `piFinSuccAbove` exposes the zeroth coordinate and the sum splits accordingly.
  constructor
  · intro hz
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    refine ⟨hz_nonneg 0, ?_, ?_⟩
    · intro i
      simpa using hz_nonneg i.succ
    · simpa [Fin.sum_univ_succ, le_sub_iff_add_le, add_comm, add_left_comm, add_assoc] using hz_sum
  · rintro ⟨hx, hy, hsum⟩
    refine ⟨?_, ?_⟩
    · intro i
      refine Fin.cases ?_ ?_ i
      · simpa using hx
      · intro j
        simpa using hy j
    · simpa [Fin.sum_univ_succ, le_sub_iff_add_le, add_comm, add_left_comm, add_assoc] using hsum

/-- Helper for Exercise 13.1.5: transporting the positive simplex through `piFinSuccAbove` gives
the head/tail set used in the slicing argument. -/
private theorem positiveSimplexTransport_preimage_eq
    (m : ℕ) (a : ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm ⁻¹'
        {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) =
      {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} := by
  ext p
  rcases p with ⟨x, y⟩
  simpa [Set.mem_preimage] using positiveSimplex_piFinSuccAbove_symm_mem_iff m a x y

/-- Helper for Exercise 13.1.5: the head/tail simplex fiber over a fixed first coordinate is the
expected lower-dimensional simplex or the empty set. -/
private theorem positiveSimplexSection_preimage_eq
    (m : ℕ) (a x : ℝ) :
    Prod.mk x ⁻¹'
        {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} =
      if 0 ≤ x then
        {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
      else ∅ := by
  ext y
  by_cases hx : 0 ≤ x
  · simp [hx]
  · simp [hx]

/-- Helper for Exercise 13.1.5: the real volume of a head/tail fiber is the simplex-section
integrand supported on `Set.Icc 0 a`. -/
private theorem positiveSimplexSection_real_eq_indicator
    (m : ℕ) (a x : ℝ) :
    volume.real
        (Prod.mk x ⁻¹'
          {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1}) =
      (Set.Icc (0 : ℝ) a).indicator
        (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x := by
  -- Proof comment: the fiber is empty off `[0,a]`, and inside `[0,a]` it is exactly the smaller
  -- simplex with threshold `a - x`.
  by_cases hx : 0 ≤ x
  · rw [positiveSimplexSection_preimage_eq, if_pos hx]
    by_cases hxa : x ≤ a
    · rw [Set.indicator_of_mem (by exact ⟨hx, hxa⟩)]
    · have hax : a - x < 0 := by linarith
      have hx_not_mem : x ∉ Set.Icc (0 : ℝ) a := by
        simp [Set.mem_Icc, hx, hxa]
      rw [positiveSimplexReal_zero_of_lt_zero m (a - x) hax]
      rw [Set.indicator_of_notMem hx_not_mem]
  · rw [positiveSimplexSection_preimage_eq, if_neg hx]
    have hx_not_mem : x ∉ Set.Icc (0 : ℝ) a := by
      simp [Set.mem_Icc, hx]
    rw [Set.indicator_of_notMem hx_not_mem]
    simp

/-- Helper for Exercise 13.1.5: slicing the `(m + 1)`-dimensional positive simplex by its first
coordinate turns the real volume into a one-dimensional integral of lower-dimensional simplex
sections. -/
private theorem positiveSimplexReal_succ_eq_intervalIntegral
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      ∫ x in 0..a,
        volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := by
  let simplex : Set (Fin (m + 1) → ℝ) :=
    {z : Fin (m + 1) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
  let headTailSet : Set (ℝ × (Fin m → ℝ)) :=
    {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1}
  let e : (ℝ × (Fin m → ℝ)) ≃ᵐ (Fin (m + 1) → ℝ) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm
  have hem : MeasurePreserving e := by
    exact (MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m + 1) ↦ ℝ) 0).symm _
  have hsimplex : MeasurableSet simplex := by
    simpa [simplex] using positiveSimplex_measurableSet (m + 1) a
  have htransport : e ⁻¹' simplex = headTailSet := by
    simpa [e, simplex, headTailSet] using positiveSimplexTransport_preimage_eq m a
  have hheadTail : MeasurableSet headTailSet := by
    rw [← htransport]
    exact hsimplex.preimage e.measurable
  have hsimplex_subset_box :
      simplex ⊆ Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ a) := by
    -- Proof comment: each coordinate is nonnegative and bounded by the full coordinate sum.
    intro z hz
    rcases hz with ⟨hz_nonneg, hz_sum⟩
    refine ⟨hz_nonneg, ?_⟩
    intro i
    have hcoord_le_sum : z i ≤ ∑ j, z j := by
      simpa using Finset.single_le_sum (fun j _ ↦ hz_nonneg j) (Finset.mem_univ i)
    linarith
  have hboxFinite :
      (volume : Measure (Fin (m + 1) → ℝ)) (Set.Icc (fun _ ↦ (0 : ℝ)) (fun _ ↦ a)) ≠ ⊤ := by
    rw [Real.volume_Icc_pi]
    simp
  have hsimplexFinite : (volume : Measure (Fin (m + 1) → ℝ)) simplex ≠ ⊤ :=
    measure_ne_top_of_subset hsimplex_subset_box hboxFinite
  have hheadTailFinite : (volume : Measure (ℝ × (Fin m → ℝ))) headTailSet ≠ ⊤ := by
    rw [← htransport, ← Measure.map_apply e.measurable hsimplex, hem.map_eq]
    exact hsimplexFinite
  have hindicator :
      Integrable (headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)))
        (volume : Measure (ℝ × (Fin m → ℝ))) := by
    exact (integrableOn_const hheadTailFinite).integrable_indicator hheadTail
  have hsection_indicator :
      ∀ x : ℝ,
        ∫ y, headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)
            ∂(volume : Measure (Fin m → ℝ)) =
          volume.real (Prod.mk x ⁻¹' headTailSet) := by
    intro x
    have hsection_eq :
        (fun y : Fin m → ℝ ↦ headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)) =
          (Prod.mk x ⁻¹' headTailSet).indicator (fun _ : Fin m → ℝ ↦ (1 : ℝ)) := by
      funext y
      simp [Set.indicator, Set.mem_preimage]
    have hsection_meas :
        MeasurableSet (Prod.mk x ⁻¹' headTailSet) := by
      rw [show Prod.mk x ⁻¹' headTailSet =
          Prod.mk x ⁻¹'
            {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1 ∧ (∀ i, 0 ≤ p.2 i) ∧ ∑ i, p.2 i ≤ a - p.1} by
          rfl]
      rw [positiveSimplexSection_preimage_eq]
      by_cases hx : 0 ≤ x
      · simpa [hx] using positiveSimplex_measurableSet m (a - x)
      · simp [hx]
    simpa [hsection_eq] using
      (integral_indicator_one
        (μ := (volume : Measure (Fin m → ℝ)))
        (s := Prod.mk x ⁻¹' headTailSet)
        hsection_meas)
  have hsection_interval :
      ∀ x : ℝ,
        volume.real (Prod.mk x ⁻¹' headTailSet) =
          (Set.Icc (0 : ℝ) a).indicator
            (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x := by
    intro x
    simpa [headTailSet] using positiveSimplexSection_real_eq_indicator m a x
  have hinterval :
      ∫ x in Set.Ioc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) =
        ∫ x in 0..a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := by
    have htmp :
        ∫ x in 0..a,
            volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
              ∂(volume : Measure ℝ) =
          ∫ x in Set.uIoc (0 : ℝ) a,
            volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
              ∂(volume : Measure ℝ) := by
      rw [intervalIntegral.intervalIntegral_eq_integral_uIoc]
      simp [ha]
    simpa [Set.uIoc_of_le ha] using htmp.symm
  -- Route correction: transport once to head-tail coordinates, then use a single Fubini step.
  calc
    volume.real simplex = ∫ z, simplex.indicator (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)) z
        ∂(volume : Measure (Fin (m + 1) → ℝ)) := by
          simpa using
            (integral_indicator_one
              (μ := (volume : Measure (Fin (m + 1) → ℝ)))
              (s := simplex)
              hsimplex).symm
    _ =
        ∫ p,
          simplex.indicator (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)) (e p)
            ∂(volume : Measure (ℝ × (Fin m → ℝ))) := by
          rw [← hem.integral_comp' (simplex.indicator
            (fun _ : Fin (m + 1) → ℝ ↦ (1 : ℝ)))]
    _ =
        ∫ p,
          headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) p
            ∂(volume : Measure (ℝ × (Fin m → ℝ))) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun p ↦ ?_)
          have hpiff : e p ∈ simplex ↔ p ∈ headTailSet := by
            rcases p with ⟨x, y⟩
            simpa [e, simplex, headTailSet] using
              positiveSimplex_piFinSuccAbove_symm_mem_iff m a x y
          by_cases hp : p ∈ headTailSet
          · have hpe : e p ∈ simplex := hpiff.mpr hp
            simp [Set.indicator, hp, hpe]
          · have hpe : e p ∉ simplex := by
              intro hpe
              exact hp (hpiff.mp hpe)
            simp [Set.indicator, hp, hpe]
    _ =
        ∫ x, ∫ y,
          headTailSet.indicator (fun _ : ℝ × (Fin m → ℝ) ↦ (1 : ℝ)) (x, y)
            ∂(volume : Measure (Fin m → ℝ)) ∂(volume : Measure ℝ) := by
          rw [Measure.volume_eq_prod, integral_prod _ hindicator]
    _ = ∫ x, volume.real (Prod.mk x ⁻¹' headTailSet) ∂(volume : Measure ℝ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall hsection_indicator)
    _ =
        ∫ x,
          (Set.Icc (0 : ℝ) a).indicator
            (fun x ↦ volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}) x
            ∂(volume : Measure ℝ) := by
          refine integral_congr_ae (Filter.Eventually.of_forall hsection_interval)
    _ =
        ∫ x in Set.Icc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) := by
          rw [integral_indicator measurableSet_Icc]
    _ =
        ∫ x in Set.Ioc (0 : ℝ) a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x}
            ∂(volume : Measure ℝ) := by
          rw [integral_Icc_eq_integral_Ioc]
    _ =
        ∫ x in 0..a,
          volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} := hinterval

/-- Helper for Exercise 13.1.5: the `m`-dimensional positive simplex with threshold `a ≥ 0` has
real volume `a ^ m / m!`. -/
private theorem positiveSimplexReal_eq_pow_div_factorial
    (m : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : Fin m → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      a ^ m / (Nat.factorial m : ℝ) := by
  induction m generalizing a with
  | zero =>
      have hset :
          {z : Fin 0 → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} = Set.univ := by
        ext z
        simp [ha]
      rw [hset]
      have huniv :
          (Set.univ : Set (Fin 0 → ℝ)) =
            Set.Icc (fun _ : Fin 0 ↦ (0 : ℝ)) (fun _ ↦ (1 : ℝ)) := by
        ext z
        simp
      rw [huniv, measureReal_def, Real.volume_Icc_pi]
      simp
  | succ m hm =>
      rw [positiveSimplexReal_succ_eq_intervalIntegral m a ha]
      have hsection :
          ∀ᵐ x ∂(volume : Measure ℝ),
            x ∈ Set.uIoc (0 : ℝ) a →
              volume.real {y : Fin m → ℝ | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ a - x} =
                (a - x) ^ m / (Nat.factorial m : ℝ) := by
        filter_upwards with x hx
        have hx' : x ∈ Set.Ioc (0 : ℝ) a := by
          simpa [Set.uIoc_of_le ha] using hx
        exact hm (a - x) (by linarith [hx'.2])
      rw [intervalIntegral.integral_congr_ae hsection]
      have hcomp :
          ∫ x in 0..a, (a - x) ^ m = ∫ x in 0..a, x ^ m := by
        simpa using
          (intervalIntegral.integral_comp_sub_left (f := fun x : ℝ ↦ x ^ m) (a := (0 : ℝ))
            (b := a) a)
      calc
        ∫ x in 0..a, (a - x) ^ m / (Nat.factorial m : ℝ) =
            (∫ x in 0..a, (a - x) ^ m) / (Nat.factorial m : ℝ) := by
              rw [intervalIntegral.integral_div]
        _ = (∫ x in 0..a, x ^ m) / (Nat.factorial m : ℝ) := by
              rw [hcomp]
        _ = (a ^ (m + 1) / (m + 1 : ℝ)) / (Nat.factorial m : ℝ) := by
              rw [integral_pow]
              ring
        _ = a ^ (m + 1) / (Nat.factorial (m + 1) : ℝ) := by
              have hm1_ne : (m + 1 : ℝ) ≠ 0 := by
                exact_mod_cast Nat.succ_ne_zero m
              have hfact_ne : (Nat.factorial m : ℝ) ≠ 0 := by
                exact_mod_cast Nat.factorial_ne_zero m
              rw [Nat.factorial_succ, Nat.cast_mul]
              field_simp [hm1_ne, hfact_ne]
              rw [Nat.cast_add, Nat.cast_one]

/-- Helper for Exercise 13.1.5: reindexing a positive simplex along a finite equivalence preserves
its real volume formula. -/
private theorem positiveSimplexReal_eq_pow_div_factorial_fintype
    (ι : Type*) [Fintype ι] (a : ℝ) (ha : 0 ≤ a) :
    volume.real {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
      a ^ Fintype.card ι / (Nat.factorial (Fintype.card ι) : ℝ) := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let E : (Fin (Fintype.card ι) → ℝ) ≃ᵐ (ι → ℝ) := MeasurableEquiv.piCongrLeft (fun _ : ι ↦ ℝ) e
  have hmap : (volume.map E) = (volume : Measure (ι → ℝ)) := by
    -- Proof comment: reindexing a finite product by `equivFin` is volume preserving.
    simpa [E, e] using
      (MeasureTheory.volume_measurePreserving_piCongrLeft (fun _ : ι ↦ ℝ) e).map_eq
  have hmeas :
      MeasurableSet {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} :=
    positiveSimplex_measurableSet_fintype ι a
  have hpreimageE :
      E ⁻¹' {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} =
        {z : Fin (Fintype.card ι) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
    -- Proof comment: after reindexing, the coordinate inequalities and total sum are identical.
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hz_nonneg, hz_sum⟩
      constructor
      · intro i
        have hzi : 0 ≤ E z (e i) := hz_nonneg (e i)
        simpa [E, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast] using hzi
      · have hsum :
            ∑ i : ι, E z i = ∑ j : Fin (Fintype.card ι), z j := by
          calc
            ∑ i : ι, E z i = ∑ i : ι, z (e.symm i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simpa [E, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
            _ = ∑ j : Fin (Fintype.card ι), z j := by
                simpa using (e.sum_comp fun i : ι ↦ z (e.symm i)).symm
        simpa [hsum] using hz_sum
    · rintro ⟨hz_nonneg, hz_sum⟩
      constructor
      · intro i
        have hzi : 0 ≤ z (e.symm i) := hz_nonneg (e.symm i)
        simpa [E, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast] using hzi
      · have hsum :
            ∑ i : ι, E z i = ∑ j : Fin (Fintype.card ι), z j := by
          calc
            ∑ i : ι, E z i = ∑ i : ι, z (e.symm i) := by
                refine Finset.sum_congr rfl ?_
                intro i hi
                simpa [E, e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
            _ = ∑ j : Fin (Fintype.card ι), z j := by
                simpa using (e.sum_comp fun i : ι ↦ z (e.symm i)).symm
        simpa [hsum] using hz_sum
  calc
    volume.real {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}
        = (volume.map E).real {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
            simp [hmap]
    _ = volume.real (E ⁻¹' {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a}) := by
          rw [MeasureTheory.map_measureReal_apply E.measurable hmeas]
    _ = volume.real {z : Fin (Fintype.card ι) → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ a} := by
          rw [hpreimageE]
    _ = a ^ Fintype.card ι / (Nat.factorial (Fintype.card ι) : ℝ) := by
          simpa using positiveSimplexReal_eq_pow_div_factorial (Fintype.card ι) a ha

/-- Helper for Exercise 13.1.5: shifting every coordinate by `ε` turns a translated simplex into a
standard nonnegative simplex with smaller threshold. -/
private theorem shiftedPositiveSimplex_preimage
    (ι : Type*) [Fintype ι] (ε t : ℝ) :
    (fun z : ι → ℝ ↦ z + fun _ ↦ ε) ⁻¹'
        {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t} =
      {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t - (Fintype.card ι : ℝ) * ε} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_setOf_eq, Pi.add_apply]
  have hsum_shift :
      ∑ i, (z i + ε) = ∑ i, z i + (Fintype.card ι : ℝ) * ε := by
    -- Proof comment: adding the same shift in every coordinate raises the simplex sum by
    -- `card(ι) * ε`.
    rw [Finset.sum_add_distrib]
    simp [Finset.card_univ, mul_comm]
  constructor
  · rintro ⟨hz_lower, hz_sum⟩
    constructor
    · intro i
      linarith [hz_lower i]
    · rw [hsum_shift] at hz_sum
      linarith
  · rintro ⟨hz_nonneg, hz_sum⟩
    constructor
    · intro i
      linarith [hz_nonneg i]
    · rw [hsum_shift]
      linarith

/-- Helper for Exercise 13.1.5: shifted positive simplices are measurable on every finite
function space. -/
private theorem shiftedPositiveSimplex_measurableSet_fintype
    (ι : Type*) [Fintype ι] (ε t : ℝ) :
    MeasurableSet {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t} := by
  have hlower : MeasurableSet {z : ι → ℝ | ∀ i, ε ≤ z i} := by
    -- Proof comment: the coordinate lower bounds form a finite intersection of measurable
    -- half-spaces.
    rw [show {z : ι → ℝ | ∀ i, ε ≤ z i} = ⋂ i, {z : ι → ℝ | ε ≤ z i} by
      ext z
      simp]
    exact MeasurableSet.iInter fun i ↦ measurable_pi_apply i measurableSet_Ici
  have hsum : MeasurableSet {z : ι → ℝ | ∑ i, z i ≤ t} := by
    -- Proof comment: the total coordinate sum is measurable on every finite function space.
    exact (prefixSum_measurable_fintype ι) measurableSet_Iic
  simpa [Set.setOf_and] using hlower.inter hsum

/-- Helper for Exercise 13.1.5: a shifted positive simplex has the translated positive-simplex
volume predicted by the simplex threshold. -/
private theorem shiftedPositiveSimplexReal_eq_pow_div_factorial
    (ι : Type*) [Fintype ι] (ε t : ℝ) (hε : 0 ≤ ε) (ht : (Fintype.card ι : ℝ) * ε ≤ t) :
    volume.real {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t} =
      (t - (Fintype.card ι : ℝ) * ε) ^ Fintype.card ι /
        (Nat.factorial (Fintype.card ι) : ℝ) := by
  have hε_nonneg : 0 ≤ ε := hε
  have hthreshold : 0 ≤ t - (Fintype.card ι : ℝ) * ε := by
    linarith [hε_nonneg, ht]
  calc
    volume.real {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t}
        = volume.real
            ((fun z : ι → ℝ ↦ z + fun _ ↦ ε) ⁻¹'
              {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t}) := by
              -- Proof comment: translation by the constant vector `ε` preserves Lebesgue volume.
              rw [measureReal_def]
              rw [← measure_preimage_add_right
                (volume : Measure (ι → ℝ))
                (fun _ ↦ ε)
                {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t}]
              rw [measureReal_def]
    _ = volume.real {z : ι → ℝ | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ t - (Fintype.card ι : ℝ) * ε} := by
          rw [shiftedPositiveSimplex_preimage]
    _ = (t - (Fintype.card ι : ℝ) * ε) ^ Fintype.card ι /
          (Nat.factorial (Fintype.card ι) : ℝ) := by
          exact positiveSimplexReal_eq_pow_div_factorial_fintype ι _ hthreshold

/-- Helper for Exercise 13.1.5: negating every coordinate preserves the volume of a shifted
positive simplex. -/
private theorem negShiftedPositiveSimplexReal_eq
    (ι : Type*) [Fintype ι] (ε t : ℝ) :
    volume.real {z : ι → ℝ | (∀ i, ε ≤ -z i) ∧ ∑ i, -z i ≤ t} =
      volume.real {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t} := by
  let A : Set (ι → ℝ) := {z : ι → ℝ | (∀ i, ε ≤ -z i) ∧ ∑ i, -z i ≤ t}
  let B : Set (ι → ℝ) := {z : ι → ℝ | (∀ i, ε ≤ z i) ∧ ∑ i, z i ≤ t}
  have hmeasB : MeasurableSet B := shiftedPositiveSimplex_measurableSet_fintype ι ε t
  have hpreimage : (fun z : ι → ℝ ↦ -z) ⁻¹' B = A := by
    -- Proof comment: negating the coordinates swaps the two shifted simplex descriptions exactly.
    ext z
    simp [A, B]
  have hmap : (volume.map (fun z : ι → ℝ ↦ -z)) = (volume : Measure (ι → ℝ)) := by
    -- Proof comment: coordinatewise negation is a measure-preserving linear isometry.
    simpa using (Measure.measurePreserving_neg (volume : Measure (ι → ℝ))).map_eq
  calc
    volume.real A = (volume.map (fun z : ι → ℝ ↦ -z)).real B := by
      rw [MeasureTheory.map_measureReal_apply measurable_neg hmeasB, hpreimage]
    _ = volume.real B := by
      simp [hmap]

/-- Helper for Exercise 13.1.5: the open standard simplex in `Fin 5 → ℝ`. -/
private def standardOpenSimplexFive : Set (Fin 5 → ℝ) :=
  {z | (∀ i, 0 < z i) ∧ ∑ i, z i < 1}

/-- Helper for Exercise 13.1.5: the closed standard simplex controlling the open model volume
bound. -/
private def standardClosedSimplexFive : Set (Fin 5 → ℝ) :=
  {z | (∀ i, 0 ≤ z i) ∧ ∑ i, z i ≤ 1}

/-- Helper for Exercise 13.1.5: the translate family `{x + C | -x ∈ C}` attached to the open
standard simplex. -/
private def simplexTranslateFamily : Set (Set (Fin 5 → ℝ)) :=
  {U | ∃ x : Fin 5 → ℝ, -x ∈ standardOpenSimplexFive ∧ U = ({x} : Set (Fin 5 → ℝ)) + standardOpenSimplexFive}

/-- Helper for Exercise 13.1.5: the fixed margin used in the quantitative simplex sign-cell lower
bound. -/
private noncomputable def simplexShrunkMargin : ℝ := (1 / 10000 : ℝ)

/-- Helper for Exercise 13.1.5: the closed shrunk sign cell indexed by `S`. -/
private noncomputable def simplexShrunkSignCell (S : Finset (Fin 5)) : Set (Fin 5 → ℝ) :=
  {z | (∀ i ∈ S, simplexShrunkMargin ≤ z i) ∧
      (∀ i ∉ S, simplexShrunkMargin ≤ -z i) ∧
      (Finset.sum S fun i ↦ z i) ≤ 1 - simplexShrunkMargin ∧
      (Finset.sum Sᶜ fun i ↦ -z i) ≤ 1 - simplexShrunkMargin}

/-- Helper for Exercise 13.1.5: the open simplex sits inside the closed simplex. -/
private lemma standardOpenSimplexFive_subset_closed :
    standardOpenSimplexFive ⊆ standardClosedSimplexFive := by
  -- Proof comment: replacing strict inequalities by weak ones gives the closed simplex.
  intro z hz
  rcases hz with ⟨hz_pos, hz_sum⟩
  exact ⟨fun i ↦ (hz_pos i).le, hz_sum.le⟩

/-- Helper for Exercise 13.1.5: the closed simplex has real volume `1 / 120`. -/
private lemma volumeReal_standardClosedSimplexFive :
    volume.real standardClosedSimplexFive = (1 / 120 : ℝ) := by
  -- Proof comment: this is the `m = 5`, `a = 1` case of the positive-simplex volume formula.
  simpa [standardClosedSimplexFive] using
    positiveSimplexReal_eq_pow_div_factorial 5 1 (by positivity)

/-- Helper for Exercise 13.1.5: the open simplex is open, bounded, convex, and not
origin-symmetric. -/
private lemma standardOpenSimplexFiveSpec :
    IsOpenBoundedConvexSet standardOpenSimplexFive ∧
      ¬ IsOriginSymmetric standardOpenSimplexFive := by
  have hcoord_open : IsOpen {z : Fin 5 → ℝ | ∀ i, 0 < z i} := by
    -- Proof comment: the coordinatewise positivity region is a finite intersection of open
    -- coordinate half-spaces.
    rw [show {z : Fin 5 → ℝ | ∀ i, 0 < z i} =
      ⋂ i ∈ (Finset.univ : Finset (Fin 5)), {z : Fin 5 → ℝ | 0 < z i} by
      ext z
      simp]
    exact isOpen_biInter_finset fun i _ ↦
      (continuous_apply i).isOpen_preimage _ isOpen_Ioi
  have hsum_open : IsOpen {z : Fin 5 → ℝ | ∑ i, z i < 1} := by
    -- Proof comment: the simplex cutoff is an open half-space for the continuous sum map.
    exact (by
      continuity :
        Continuous fun z : Fin 5 → ℝ ↦ ∑ i, z i).isOpen_preimage _ isOpen_Iio
  have hbounded : Bornology.IsBounded standardOpenSimplexFive := by
    -- Proof comment: every coordinate is positive and bounded above by the total simplex sum, so
    -- all coordinates lie in `(-1, 1)`.
    refine bounded_of_coordinate_bounds_pi (show (0 : ℝ) ≤ 1 by norm_num) ?_
    intro z hz i
    rcases hz with ⟨hz_pos, hz_sum_lt⟩
    have hz_sum_nonneg : 0 ≤ ∑ j, z j := by
      refine Finset.sum_nonneg ?_
      intro j hj
      exact (hz_pos j).le
    have hzi_lt_one : z i < 1 := lt_of_le_of_lt (Finset.single_le_sum (fun j _ ↦ (hz_pos j).le) (by
      simp)) hz_sum_lt
    have hzi_nonneg : 0 ≤ z i := (hz_pos i).le
    rw [Real.norm_eq_abs, abs_of_nonneg hzi_nonneg]
    linarith
  have hconvex : Convex ℝ standardOpenSimplexFive := by
    -- Proof comment: convex combinations preserve coordinate positivity and keep the total sum
    -- below `1` because both simplex sums are already `< 1`.
    intro x hx y hy a b ha hb hab
    rcases hx with ⟨hx_pos, hx_sum⟩
    rcases hy with ⟨hy_pos, hy_sum⟩
    constructor
    · intro i
      -- Proof comment: one positive coordinate survives because `a + b = 1` with both weights
      -- nonnegative, so they cannot both vanish.
      change 0 < a * x i + b * y i
      have hab_pos : 0 < a ∨ 0 < b := by
        by_cases ha_zero : a = 0
        · right
          linarith
        · left
          exact lt_of_le_of_ne ha (Ne.symm ha_zero)
      cases hab_pos with
      | inl ha_pos =>
          have hax : 0 < a * x i := mul_pos ha_pos (hx_pos i)
          have hby : 0 ≤ b * y i := mul_nonneg hb (hy_pos i).le
          linarith
      | inr hb_pos =>
          have hax : 0 ≤ a * x i := mul_nonneg ha (hx_pos i).le
          have hby : 0 < b * y i := mul_pos hb_pos (hy_pos i)
          linarith
    · have hsum_eq :
          ∑ i, (a • x + b • y) i = a * (∑ i, x i) + b * (∑ i, y i) := by
        simp [Finset.sum_add_distrib, Finset.mul_sum]
      rw [hsum_eq]
      have hab_pos : 0 < a ∨ 0 < b := by
        by_cases ha_zero : a = 0
        · right
          linarith
        · left
          exact lt_of_le_of_ne ha (Ne.symm ha_zero)
      have hx_sum_le : ∑ i, x i ≤ 1 := hx_sum.le
      have hy_sum_le : ∑ i, y i ≤ 1 := hy_sum.le
      cases hab_pos with
      | inl ha_pos =>
          have hax : a * (∑ i, x i) < a * 1 := mul_lt_mul_of_pos_left hx_sum ha_pos
          have hby : b * (∑ i, y i) ≤ b * 1 := mul_le_mul_of_nonneg_left hy_sum_le hb
          have hlt : a * (∑ i, x i) + b * (∑ i, y i) < a * 1 + b * 1 :=
            add_lt_add_of_lt_of_le hax hby
          simpa [hab] using hlt
      | inr hb_pos =>
          have hax : a * (∑ i, x i) ≤ a * 1 := mul_le_mul_of_nonneg_left hx_sum_le ha
          have hby : b * (∑ i, y i) < b * 1 := mul_lt_mul_of_pos_left hy_sum hb_pos
          have hlt : a * (∑ i, x i) + b * (∑ i, y i) < a * 1 + b * 1 :=
            add_lt_add_of_le_of_lt hax hby
          simpa [hab] using hlt
  refine ⟨⟨?_, hbounded, hconvex⟩, ?_⟩
  · -- Proof comment: the open simplex is the intersection of the open positivity region with the
    -- open sum half-space.
    simpa [standardOpenSimplexFive, Set.setOf_and] using hcoord_open.inter hsum_open
  · -- Proof comment: the constant vector `1/10` belongs to the simplex, but its negation fails the
    -- positivity condition, so the model is not origin-symmetric.
    intro hsymm
    let z : Fin 5 → ℝ := fun _ ↦ (1 / 10 : ℝ)
    have hz_mem : z ∈ standardOpenSimplexFive := by
      constructor
      · intro i
        norm_num [z]
      · norm_num [z]
    have hneg_mem : -z ∈ standardOpenSimplexFive := hsymm hz_mem
    have hneg_pos := hneg_mem.1 0
    norm_num [z] at hneg_pos

/-- Helper for Exercise 13.1.5: every member of the simplex translate family contains the origin
and has real volume at most `1 / 120`. -/
private lemma simplexTranslateFamilyMemberSpec
    {U : Set (Fin 5 → ℝ)} (hU : U ∈ simplexTranslateFamily) :
    (0 : Fin 5 → ℝ) ∈ U ∧ volume.real U ≤ (1 / 120 : ℝ) := by
  rcases hU with ⟨x, hx, rfl⟩
  have hmeas : MeasurableSet standardOpenSimplexFive := standardOpenSimplexFiveSpec.1.1.measurableSet
  have hclosed_fin : volume standardClosedSimplexFive ≠ ⊤ := by
    -- Proof comment: the closed simplex already has explicit finite real volume `1 / 120`.
    intro htop
    have hzero : volume.real standardClosedSimplexFive = 0 := by
      simp [measureReal_def, htop]
    linarith [volumeReal_standardClosedSimplexFive]
  have hopen_le :
      volume.real standardOpenSimplexFive ≤ (1 / 120 : ℝ) := by
    -- Proof comment: the open simplex sits inside the closed simplex of known volume.
    rw [← volumeReal_standardClosedSimplexFive]
    exact measureReal_mono standardOpenSimplexFive_subset_closed hclosed_fin
  constructor
  · -- Proof comment: the defining translate vector is chosen so that `0 = x + (-x)` lies in the
    -- translated simplex copy.
    refine ⟨x, by simp, -x, hx, ?_⟩
    simp
  · -- Proof comment: translation preserves real volume, so the same `1 / 120` upper bound applies
    -- to every family member.
    calc
      volume.real (({x} : Set (Fin 5 → ℝ)) + standardOpenSimplexFive)
          = volume.real (({x} : Set (Fin 5 → ℝ)) + (1 : ℝ) • standardOpenSimplexFive) := by
              simp
      _ = (1 : ℝ) ^ 5 * volume.real standardOpenSimplexFive := by
            simpa using translatedSmul_volumeReal hmeas x (show (0 : ℝ) < 1 by norm_num)
      _ = volume.real standardOpenSimplexFive := by simp
      _ ≤ (1 / 120 : ℝ) := hopen_le

/-- Helper for Exercise 13.1.5: the simplex translate family is a common-model family with finite
union measure. -/
private lemma simplexTranslateFamilySpec :
    IsAsymmetricCommonHomotheticModel standardOpenSimplexFive simplexTranslateFamily ∧
      HasFiniteUnionMeasure simplexTranslateFamily := by
  refine ⟨?_, ?_⟩
  · -- Proof comment: every family member is a translate of the same open simplex by scale `1`,
    -- and the simplex was already shown to be non-symmetric.
    refine ⟨standardOpenSimplexFiveSpec.1, standardOpenSimplexFiveSpec.2, ?_⟩
    intro U hU
    rcases hU with ⟨x, hx, rfl⟩
    exact ⟨x, 1, by norm_num, by simp⟩
  · let box : Set (Fin 5 → ℝ) := {z | ∀ i, |z i| < 1}
    have hbox_bounded : Bornology.IsBounded box := by
      -- Proof comment: the open unit box has uniform coordinate bound `1`, hence finite volume.
      refine bounded_of_coordinate_bounds_pi (show (0 : ℝ) ≤ 1 by norm_num) ?_
      intro z hz i
      rw [Real.norm_eq_abs]
      exact (hz i).le
    have hsubset_box : ⋃₀ simplexTranslateFamily ⊆ box := by
      -- Proof comment: points in the union are differences of two simplex points, so every
      -- coordinate lies in `(-1, 1)`.
      intro z hz
      rcases mem_sUnion.1 hz with ⟨U, hU, hzU⟩
      rcases hU with ⟨c, hc, hU_eq⟩
      have hzU' : z ∈ ({c} : Set (Fin 5 → ℝ)) + standardOpenSimplexFive := by
        simpa [hU_eq] using hzU
      rcases hzU' with ⟨x, hx, y, hy, hzy⟩
      rcases hx with rfl
      intro i
      have hy_pos : 0 < y i := hy.1 i
      have hy_lt_one : y i < 1 := by
        exact lt_of_le_of_lt
          (Finset.single_le_sum (fun j _ ↦ (hy.1 j).le) (by simp))
          hy.2
      have hx_pos : 0 < (-x) i := hc.1 i
      have hx_lt_one : (-x) i < 1 := by
        exact lt_of_le_of_lt
          (Finset.single_le_sum (fun j _ ↦ (hc.1 j).le) (by simp))
          hc.2
      have hzi : z i = y i - (-x i) := by
        have hcoord : z i = x i + y i := by
          simpa using (congrArg (fun w : Fin 5 → ℝ ↦ w i) hzy).symm
        calc
          z i = x i + y i := hcoord
          _ = y i - (-x i) := by ring
      rw [abs_lt]
      constructor
      · have hlow : -1 < y i - (-x i) := by
          have hnegx_gt : -1 < -(-x i) := by
            simpa using neg_lt_neg hx_lt_one
          have htmp : -1 + 0 < -(-x i) + y i := add_lt_add hnegx_gt hy_pos
          simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htmp
        simpa [hzi] using hlow
      · have hhigh : y i - (-x i) < 1 := by
          have hnegx_lt : -(-x i) < 0 := by
            simpa using neg_lt_neg hx_pos
          have htmp : y i + -(-x i) < 1 + 0 := add_lt_add hy_lt_one hnegx_lt
          simpa [sub_eq_add_neg, add_assoc] using htmp
        simpa [hzi] using hhigh
    exact lt_of_le_of_lt (measure_mono hsubset_box) hbox_bounded.measure_lt_top

/-- Helper for Exercise 13.1.5: any finite pairwise disjoint simplex-translate subfamily has total
real volume at most `1 / 120`. -/
private lemma simplexTranslateFamilySelectionBound
    (s : Finset (Set (Fin 5 → ℝ))) (hs_subset : (↑s : Set (Set (Fin 5 → ℝ))) ⊆ simplexTranslateFamily)
    (hs_disj : (↑s : Set (Set (Fin 5 → ℝ))).PairwiseDisjoint id) :
    s.sum (fun U ↦ volume.real U) ≤ (1 / 120 : ℝ) := by
  classical
  by_cases hs_empty : s = ∅
  · -- Proof comment: the empty selection contributes zero volume.
    simp [hs_empty]
  · rcases Finset.nonempty_iff_ne_empty.mpr hs_empty with ⟨U₀, hU₀⟩
    have hall : ∀ U ∈ s, U = U₀ := by
      -- Proof comment: every family member contains `0`, so pairwise disjointness forces any
      -- nonempty finite subfamily to collapse to one set.
      intro U hU
      by_cases hEq : U = U₀
      · exact hEq
      · have hdisj : Disjoint U U₀ :=
          hs_disj (by simpa using hU) (by simpa using hU₀) hEq
        have hzeroU : (0 : Fin 5 → ℝ) ∈ U :=
          (simplexTranslateFamilyMemberSpec (hs_subset (by simpa using hU))).1
        have hzeroU₀ : (0 : Fin 5 → ℝ) ∈ U₀ :=
          (simplexTranslateFamilyMemberSpec (hs_subset (by simpa using hU₀))).1
        exact False.elim ((Set.disjoint_left.mp hdisj) hzeroU hzeroU₀)
    have hs_singleton : s = {U₀} := Finset.eq_singleton_iff_unique_mem.2 ⟨hU₀, hall⟩
    calc
      s.sum (fun U ↦ volume.real U)
          = ({U₀} : Finset (Set (Fin 5 → ℝ))).sum (fun U ↦ volume.real U) := by
              rw [hs_singleton]
      _ = volume.real U₀ := by simp
      _ ≤ (1 / 120 : ℝ) := (simplexTranslateFamilyMemberSpec (hs_subset (by simpa using hU₀))).2

/-- Helper for Exercise 13.1.5: distinct sign cells are disjoint because they impose incompatible
strict signs on at least one coordinate. -/
private lemma simplexShrunkSignCell_pairwiseDisjoint :
    PairwiseDisjoint (↑(Finset.univ.powerset : Finset (Finset (Fin 5)))) simplexShrunkSignCell := by
  intro S hS T hT hST
  change Disjoint (simplexShrunkSignCell S) (simplexShrunkSignCell T)
  rw [Set.disjoint_left]
  intro z hzS hzT
  have hmargin_pos : 0 < simplexShrunkMargin := by
    norm_num [simplexShrunkMargin]
  have hdiff : ∃ i : Fin 5, ¬ (i ∈ S ↔ i ∈ T) := by
    by_contra hnodiff
    apply hST
    ext i
    exact not_not.mp (not_exists.mp hnodiff i)
  rcases hdiff with ⟨i, hi⟩
  rcases hzS with ⟨hzS_pos, hzS_neg, -, -⟩
  rcases hzT with ⟨hzT_pos, hzT_neg, -, -⟩
  by_cases hiS : i ∈ S <;> by_cases hiT : i ∈ T
  · exact (hi (by simp [hiS, hiT])).elim
  · have hz_lower : simplexShrunkMargin ≤ z i := hzS_pos i hiS
    have hz_upper : simplexShrunkMargin ≤ -z i := hzT_neg i hiT
    linarith
  · have hz_lower : simplexShrunkMargin ≤ z i := hzT_pos i hiT
    have hz_upper : simplexShrunkMargin ≤ -z i := hzS_neg i hiS
    linarith
  · exact (hi (by simp [hiS, hiT])).elim

/-- Helper for Exercise 13.1.5: every shrunk sign cell lies inside the simplex translate union. -/
private lemma simplexShrunkSignCell_subset_sUnion_family
    (S : Finset (Fin 5)) :
    simplexShrunkSignCell S ⊆ ⋃₀ simplexTranslateFamily := by
  intro z hz
  rcases hz with ⟨hz_pos, hz_neg, hz_sum_pos, hz_sum_neg⟩
  let δ : ℝ := simplexShrunkMargin / 10
  let u : Fin 5 → ℝ := fun i ↦ if i ∈ S then z i + δ else δ
  let v : Fin 5 → ℝ := fun i ↦ if i ∈ S then δ else -z i + δ
  have hmargin_pos : 0 < simplexShrunkMargin := by
    norm_num [simplexShrunkMargin]
  have hδ_pos : 0 < δ := by
    dsimp [δ]
    positivity
  have hu_pos : ∀ i, 0 < u i := by
    -- Proof comment: every positive-block coordinate stays above the cell margin, and every other
    -- coordinate is the auxiliary bump `δ`.
    intro i
    by_cases hi : i ∈ S
    · dsimp [u]
      rw [if_pos hi]
      linarith [hz_pos i hi, hδ_pos]
    · dsimp [u]
      rw [if_neg hi]
      exact hδ_pos
  have hv_pos : ∀ i, 0 < v i := by
    -- Proof comment: on the negative block, the cell gives a lower bound on `-z i`, and on the
    -- positive block we again use the auxiliary bump `δ`.
    intro i
    by_cases hi : i ∈ S
    · dsimp [v]
      rw [if_pos hi]
      exact hδ_pos
    · dsimp [v]
      rw [if_neg hi]
      linarith [hz_neg i hi, hδ_pos]
  have hu_sum : (∑ i, u i) = (Finset.sum S fun i ↦ z i) + (5 : ℝ) * δ := by
    -- Proof comment: `u` contributes the `S`-sum of `z` plus one copy of `δ` in every coordinate.
    rw [show (∑ i, u i) = ∑ i, ((if i ∈ S then z i else 0) + δ) by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hiS : i ∈ S <;> simp [u, hiS, add_comm, add_left_comm, add_assoc]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    simp [δ, Finset.card_univ]
  have hv_sum : (∑ i, v i) = (Finset.sum Sᶜ fun i ↦ -z i) + (5 : ℝ) * δ := by
    -- Proof comment: the same decomposition works for the negative block after taking `-z`.
    rw [show (∑ i, v i) = ∑ i, ((if i ∈ Sᶜ then -z i else 0) + δ) by
      refine Finset.sum_congr rfl ?_
      intro i hi
      by_cases hiS : i ∈ S <;> simp [v, hiS, add_comm, add_left_comm, add_assoc]]
    rw [Finset.sum_add_distrib, Finset.sum_ite_mem]
    simp [δ, Finset.card_univ]
  have hu_sum_lt : ∑ i, u i < 1 := by
    calc
      ∑ i, u i = (Finset.sum S fun i ↦ z i) + (5 : ℝ) * δ := hu_sum
      _ ≤ (1 - simplexShrunkMargin) + (5 : ℝ) * δ := by gcongr
      _ = 1 - simplexShrunkMargin / 2 := by
            dsimp [δ, simplexShrunkMargin]
            ring
      _ < 1 := by linarith
  have hv_sum_lt : ∑ i, v i < 1 := by
    calc
      ∑ i, v i = (Finset.sum Sᶜ fun i ↦ -z i) + (5 : ℝ) * δ := hv_sum
      _ ≤ (1 - simplexShrunkMargin) + (5 : ℝ) * δ := by gcongr
      _ = 1 - simplexShrunkMargin / 2 := by
            dsimp [δ, simplexShrunkMargin]
            ring
      _ < 1 := by linarith
  have hu_mem : u ∈ standardOpenSimplexFive := ⟨hu_pos, hu_sum_lt⟩
  have hv_mem : v ∈ standardOpenSimplexFive := ⟨hv_pos, hv_sum_lt⟩
  have hz_eq : z = -v + u := by
    -- Proof comment: the two auxiliary simplex points were chosen so that their difference is
    -- exactly the original sign-cell point.
    ext i
    by_cases hi : i ∈ S <;> simp [u, v, hi, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
  refine mem_sUnion.2 ⟨({-v} : Set (Fin 5 → ℝ)) + standardOpenSimplexFive, ?_, ?_⟩
  · -- Proof comment: `-v` is an allowed translate center because `v` itself lies in the open
    -- simplex.
    exact ⟨-v, by simpa using hv_mem, rfl⟩
  · -- Proof comment: the sign-cell point is exactly the translate center plus the positive simplex
    -- point `u`.
    refine ⟨-v, by simp, u, hu_mem, ?_⟩
    exact hz_eq.symm

/-- Helper for Exercise 13.1.5: summing over the subtype of elements of `S` agrees with summing
over the finite set `S` itself. -/
private lemma sum_subtype_mem_eq_sum
    (S : Finset (Fin 5)) (z : Fin 5 → ℝ) :
    (Finset.univ.sum fun i : (Subtype fun i : Fin 5 ↦ i ∈ S) ↦ z i) = S.sum z := by
  -- Proof comment: `S.attach` enumerates the subtype `i ∈ S`, so both finite sums have the same
  -- terms.
  rw [← Finset.attach_eq_univ]
  exact S.sum_attach fun i ↦ z i

/-- Helper for Exercise 13.1.5: summing over the subtype of indices outside `S` agrees with the
sum over the finset complement `Sᶜ`. -/
private lemma sum_subtype_notMem_eq_sum_compl
    (S : Finset (Fin 5)) (z : Fin 5 → ℝ) :
    (Finset.univ.sum fun i : (Subtype fun i : Fin 5 ↦ i ∉ S) ↦ z i) = Sᶜ.sum z := by
  classical
  let e : ({i : Fin 5 // i ∉ S}) ≃ ({i : Fin 5 // i ∈ Sᶜ}) :=
    Equiv.subtypeEquivRight fun i ↦ by simp
  -- Route correction: the old route tried to let Lean identify `{i // i ∉ S}` with
  -- `{i // i ∈ Sᶜ}` definitionally; this explicit equivalence is the stable bridge.
  calc
    (Finset.univ.sum fun i : (Subtype fun i : Fin 5 ↦ i ∉ S) ↦ z i)
        = Finset.univ.sum fun j : ↥Sᶜ ↦ z j := by
            simpa [e] using (e.sum_comp fun j : ↥Sᶜ ↦ z j)
    _ = Sᶜ.sum z := by
          rw [← Finset.attach_eq_univ]
          exact Sᶜ.sum_attach fun i ↦ z i

/-- Helper for Exercise 13.1.5: the subtype indexed by `S` has cardinality `S.card`. -/
private lemma card_subtype_mem_eq_card
    (S : Finset (Fin 5)) :
    Fintype.card ({i : Fin 5 // i ∈ S}) = S.card := by
  -- Proof comment: the subtype is exactly the finite set `S` viewed as an attached finset.
  simpa using
    (Fintype.card_ofFinset (p := {i : Fin 5 | i ∈ S}) S fun i ↦ by simp)

/-- Helper for Exercise 13.1.5: the subtype indexed by `i ∉ S` has cardinality `5 - S.card`. -/
private lemma card_subtype_notMem_eq_card_compl
    (S : Finset (Fin 5)) :
    Fintype.card ({i : Fin 5 // i ∉ S}) = 5 - S.card := by
  classical
  let e : ({i : Fin 5 // i ∉ S}) ≃ ({i : Fin 5 // i ∈ Sᶜ}) :=
    Equiv.subtypeEquivRight fun i ↦ by simp
  -- Proof comment: first replace the complement subtype by the literal subtype of `Sᶜ`, then use
  -- the standard `Finset.card_compl` identity in `Fin 5`.
  calc
    Fintype.card {i // i ∉ S} = Fintype.card {i // i ∈ Sᶜ} := Fintype.card_congr e
    _ = Sᶜ.card := by
          simpa using
            (Fintype.card_ofFinset (p := {i : Fin 5 | i ∈ Sᶜ}) Sᶜ fun i ↦ by simp)
    _ = 5 - S.card := by simpa using (Finset.card_compl S)

/-- Helper for Exercise 13.1.5: every shrunk sign cell is measurable. -/
private lemma simplexShrunkSignCell_measurableSet
    (S : Finset (Fin 5)) :
    MeasurableSet (simplexShrunkSignCell S) := by
  have hpos :
      MeasurableSet {z : Fin 5 → ℝ | ∀ i ∈ S, simplexShrunkMargin ≤ z i} := by
    -- Proof comment: the positive-block constraints are a finite intersection of coordinate
    -- half-spaces.
    rw [show {z : Fin 5 → ℝ | ∀ i ∈ S, simplexShrunkMargin ≤ z i} =
      ⋂ i ∈ S, {z : Fin 5 → ℝ | simplexShrunkMargin ≤ z i} by
      ext z
      simp]
    exact (isClosed_biInter fun i hi ↦
      isClosed_Ici.preimage (continuous_apply i)).measurableSet
  have hneg :
      MeasurableSet {z : Fin 5 → ℝ | ∀ i ∉ S, simplexShrunkMargin ≤ -z i} := by
    -- Proof comment: the negative-block constraints are the same finite-intersection argument
    -- after composing each coordinate projection with negation.
    rw [show {z : Fin 5 → ℝ | ∀ i ∉ S, simplexShrunkMargin ≤ -z i} =
      ⋂ i ∈ Sᶜ, {z : Fin 5 → ℝ | simplexShrunkMargin ≤ -z i} by
      ext z
      simp]
    exact (isClosed_biInter fun i hi ↦
      isClosed_Ici.preimage (continuous_neg.comp (continuous_apply i))).measurableSet
  have hsumPos :
      MeasurableSet {z : Fin 5 → ℝ | (Finset.sum S fun i ↦ z i) ≤ 1 - simplexShrunkMargin} := by
    -- Proof comment: the partial coordinate sum is continuous, so its lower half-space is
    -- measurable.
    exact (by
      continuity :
        Continuous fun z : Fin 5 → ℝ ↦ Finset.sum S fun i ↦ z i).measurable measurableSet_Iic
  have hsumNeg :
      MeasurableSet
        {z : Fin 5 → ℝ | (Finset.sum Sᶜ fun i ↦ -z i) ≤ 1 - simplexShrunkMargin} := by
    -- Proof comment: the same continuity argument applies to the complementary negative-block sum.
    exact (by
      continuity :
        Continuous fun z : Fin 5 → ℝ ↦ Finset.sum Sᶜ fun i ↦ -z i).measurable measurableSet_Iic
  -- Proof comment: the sign cell is the intersection of the two blockwise lower-bound regions and
  -- the two blockwise simplex-sum sublevels.
  have hcell :
      simplexShrunkSignCell S =
        {z : Fin 5 → ℝ | ∀ i ∈ S, simplexShrunkMargin ≤ z i} ∩
          ({z : Fin 5 → ℝ | ∀ i ∉ S, simplexShrunkMargin ≤ -z i} ∩
            ({z : Fin 5 → ℝ | (Finset.sum S fun i ↦ z i) ≤ 1 - simplexShrunkMargin} ∩
              {z : Fin 5 → ℝ | (Finset.sum Sᶜ fun i ↦ -z i) ≤ 1 - simplexShrunkMargin})) := by
    ext z
    simp [simplexShrunkSignCell, and_assoc]
  rw [hcell]
  exact hpos.inter (hneg.inter (hsumPos.inter hsumNeg))

/-- Helper for Exercise 13.1.5: splitting coordinates by membership in `S` turns sign-cell
membership into independent shifted-simplex constraints on the two subtype blocks. -/
private lemma simplexShrunkSignCell_splitMem_iff
    (S : Finset (Fin 5)) (z : Fin 5 → ℝ) :
    let e :
        (Fin 5 → ℝ) ≃ᵐ (({i : Fin 5 // i ∈ S} → ℝ) × ({i : Fin 5 // i ∉ S} → ℝ)) :=
      MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin 5 ↦ ℝ) (fun i ↦ i ∈ S)
    let A : Set ({i : Fin 5 // i ∈ S} → ℝ) :=
      {x | (∀ i, simplexShrunkMargin ≤ x i) ∧ ∑ i, x i ≤ 1 - simplexShrunkMargin}
    let B : Set ({i : Fin 5 // i ∉ S} → ℝ) :=
      {y | (∀ i, simplexShrunkMargin ≤ -y i) ∧ ∑ i, -y i ≤ 1 - simplexShrunkMargin}
    e z ∈ A ×ˢ B ↔ z ∈ simplexShrunkSignCell S := by
  -- Proof comment: after one coordinate split, the two blockwise inequalities are literally the
  -- sign-cell conditions, and the subtype sums reduce with the dedicated summation bridges.
  constructor
  · rintro ⟨hx, hy⟩
    rcases hx with ⟨hx_lower, hx_sum⟩
    rcases hy with ⟨hy_lower, hy_sum⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro i hi
      exact hx_lower ⟨i, hi⟩
    · intro i hi
      exact hy_lower ⟨i, hi⟩
    · simpa [Finset.sum_attach] using hx_sum
    · simpa [sum_subtype_notMem_eq_sum_compl] using hy_sum
  · rintro ⟨hz_pos, hz_neg, hz_sum_pos, hz_sum_neg⟩
    refine ⟨?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        exact hz_pos i i.property
      · simpa [Finset.sum_attach] using hz_sum_pos
    · refine ⟨?_, ?_⟩
      · intro i
        exact hz_neg i i.property
      · simpa [sum_subtype_notMem_eq_sum_compl] using hz_sum_neg

/-- Helper for Exercise 13.1.5: the finite product Lebesgue measure is independent of the chosen
`Fintype` witness. -/
private lemma measurePiInstIrrel {ι : Type*} (inst₁ inst₂ : Fintype ι) :
    @Measure.pi ι (fun _ ↦ ℝ) inst₁ (fun _ ↦ borel ℝ) (fun _ ↦ (volume : Measure ℝ)) =
      @Measure.pi ι (fun _ ↦ ℝ) inst₂ (fun _ ↦ borel ℝ) (fun _ ↦ (volume : Measure ℝ)) := by
  let μ : ι → Measure ℝ := fun _ ↦ volume
  letI : Fintype ι := inst₁
  -- Proof comment: both finite products agree on measurable rectangles, so `Measure.pi_eq`
  -- identifies them without unfolding the `Fintype` implementation.
  apply Measure.pi_eq (μ := μ)
  intro s hs
  letI : Fintype ι := inst₂
  rw [Measure.pi_pi]
  simp [μ]
  have hinst : inst₂ = inst₁ := Subsingleton.elim _ _
  cases hinst
  rfl

/-- Helper for Exercise 13.1.5: Lebesgue volume on a finite function space is independent of the
chosen `Fintype` witness. -/
private lemma volumePiInstIrrel {ι : Type*} (inst₁ inst₂ : Fintype ι) :
    @volume (ι → ℝ) (@MeasureSpace.pi ι inst₁ (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace)) =
      @volume (ι → ℝ) (@MeasureSpace.pi ι inst₂ (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace)) := by
  -- Proof comment: finite product Lebesgue measure depends only on the underlying finite type, so
  -- the two `Fintype` structures are compared at the explicit `Measure.pi` level.
  change
    @Measure.pi ι (fun _ ↦ ℝ) inst₁ (fun _ ↦ borel ℝ) (fun _ ↦ (volume : Measure ℝ)) =
      @Measure.pi ι (fun _ ↦ ℝ) inst₂ (fun _ ↦ borel ℝ) (fun _ ↦ (volume : Measure ℝ))
  exact measurePiInstIrrel inst₁ inst₂

/-- Helper for Exercise 13.1.5: the split-product volume only depends on the underlying subtype,
not on whether the positive block uses `Subtype.fintype` or `Finset.Subtype.fintype`. -/
private lemma splitProductVolumeEqFinsetSubtypeVolume (S : Finset (Fin 5)) :
    @volume ((↥S → ℝ) × ({ i : Fin 5 // i ∉ S } → ℝ))
        (@Measure.prod.measureSpace (↥S → ℝ) ({ i : Fin 5 // i ∉ S } → ℝ)
          (@MeasureSpace.pi (↥S)
            (Subtype.fintype (fun i : Fin 5 ↦ i ∈ S))
            (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))
          MeasureSpace.pi) =
      @volume ((↥S → ℝ) × ({ i : Fin 5 // i ∉ S } → ℝ))
        (@Measure.prod.measureSpace (↥S → ℝ) ({ i : Fin 5 // i ∉ S } → ℝ)
          (@MeasureSpace.pi (↥S)
            (Finset.Subtype.fintype S)
            (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))
          MeasureSpace.pi) := by
  -- Proof comment: once the first block volumes are identified by instance irrelevance, the
  -- enclosing product-space volumes agree definitionally.
  have hpi :
      @volume (↥S → ℝ)
          (@MeasureSpace.pi (↥S)
            (Subtype.fintype (fun i : Fin 5 ↦ i ∈ S))
            (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace)) =
        @volume (↥S → ℝ)
          (@MeasureSpace.pi (↥S)
            (Finset.Subtype.fintype S)
            (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace)) :=
    volumePiInstIrrel
      (ι := ↥S)
      (Subtype.fintype (fun i : Fin 5 ↦ i ∈ S))
      (Finset.Subtype.fintype S)
  change
    (@volume (↥S → ℝ)
        (@MeasureSpace.pi (↥S)
          (Subtype.fintype (fun i : Fin 5 ↦ i ∈ S))
          (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))).prod
      (volume : Measure ({ i : Fin 5 // i ∉ S } → ℝ)) =
    (@volume (↥S → ℝ)
        (@MeasureSpace.pi (↥S)
          (Finset.Subtype.fintype S)
          (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))).prod
      (volume : Measure ({ i : Fin 5 // i ∉ S } → ℝ))
  exact congrArg
    (fun μ : Measure (↥S → ℝ) ↦ μ.prod (volume : Measure ({ i : Fin 5 // i ∉ S } → ℝ)))
    hpi

/-- Helper for Exercise 13.1.5: each shrunk sign cell has the product volume dictated by its
positive and negative coordinate blocks. -/
private lemma volumeReal_simplexShrunkSignCell
    (S : Finset (Fin 5)) :
    volume.real (simplexShrunkSignCell S) =
      ((1 - ((S.card : ℝ) + 1) * simplexShrunkMargin) ^ S.card / (Nat.factorial S.card : ℝ)) *
        ((1 - (((5 - S.card : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - S.card) /
          (Nat.factorial (5 - S.card) : ℝ)) := by
  let e :
      (Fin 5 → ℝ) ≃ᵐ
        ((Subtype (fun i : Fin 5 ↦ i ∈ S) → ℝ) × (Subtype (fun i : Fin 5 ↦ i ∉ S) → ℝ)) :=
    MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin 5 ↦ ℝ) (fun i ↦ i ∈ S)
  let A : Set (Subtype (fun i : Fin 5 ↦ i ∈ S) → ℝ) :=
    {x | (∀ i, simplexShrunkMargin ≤ x i) ∧ ∑ i, x i ≤ 1 - simplexShrunkMargin}
  let B : Set (Subtype (fun i : Fin 5 ↦ i ∉ S) → ℝ) :=
    {y | (∀ i, simplexShrunkMargin ≤ -y i) ∧ ∑ i, -y i ≤ 1 - simplexShrunkMargin}
  -- Route correction: the stable bridge is the one-shot split `e`; both block volumes stay on the
  -- subtype coordinate spaces, so no later reindexing transport is needed.
  have hpreimage : e ⁻¹' (A ×ˢ B) = simplexShrunkSignCell S := by
    ext z
    simpa [e, A, B] using (simplexShrunkSignCell_splitMem_iff S z)
  have hA_meas : MeasurableSet A := by
    -- Proof comment: the positive block is exactly a shifted simplex on the `S`-coordinates.
    dsimp [A]
    exact shiftedPositiveSimplex_measurableSet_fintype
      ({i : Fin 5 // i ∈ S}) simplexShrunkMargin (1 - simplexShrunkMargin)
  have hB_meas : MeasurableSet B := by
    -- Proof comment: the negative block has the same shifted-simplex shape after negating the
    -- coordinates.
    let Bpos : Set (Subtype (fun i : Fin 5 ↦ i ∉ S) → ℝ) :=
      {y | (∀ i, simplexShrunkMargin ≤ y i) ∧ ∑ i, y i ≤ 1 - simplexShrunkMargin}
    have hBpos : MeasurableSet Bpos := by
      dsimp [Bpos]
      exact shiftedPositiveSimplex_measurableSet_fintype
        ({i : Fin 5 // i ∉ S}) simplexShrunkMargin (1 - simplexShrunkMargin)
    -- Proof comment: `B` is the preimage of the positive shifted simplex under coordinatewise
    -- negation.
    simpa [B, Bpos] using
      (hBpos.preimage
        (show Measurable fun y : {i : Fin 5 // i ∉ S} → ℝ => -y from measurable_neg))
  have hmargin_nonneg : 0 ≤ simplexShrunkMargin := by
    norm_num [simplexShrunkMargin]
  have hA_threshold :
      (Fintype.card ({i : Fin 5 // i ∈ S}) : ℝ) * simplexShrunkMargin ≤
        1 - simplexShrunkMargin := by
    -- Proof comment: at most five positive-block coordinates can contribute to the shifted
    -- simplex threshold.
    rw [card_subtype_mem_eq_card]
    have hcard : (S.card : ℝ) ≤ 5 := by
      exact_mod_cast Finset.card_le_univ S
    norm_num [simplexShrunkMargin] at ⊢
    linarith
  have hB_threshold :
      (Fintype.card ({i : Fin 5 // i ∉ S}) : ℝ) * simplexShrunkMargin ≤
        1 - simplexShrunkMargin := by
    -- Proof comment: the complementary block has cardinality `5 - S.card`, so the same numerical
    -- bound applies.
    rw [card_subtype_notMem_eq_card_compl]
    have hcard : ((5 - S.card : ℕ) : ℝ) ≤ 5 := by
      exact_mod_cast Nat.sub_le 5 S.card
    norm_num [simplexShrunkMargin] at ⊢
    linarith
  have hmap_apply :
      volume.map e (A ×ˢ B) = volume (A ×ˢ B) := by
    change
      volume.map
          (MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin 5 ↦ ℝ) (fun i ↦ i ∈ S))
          (A ×ˢ B) = volume (A ×ˢ B)
    rw [(MeasureTheory.volume_preserving_piEquivPiSubtypeProd
      (fun _ : Fin 5 ↦ ℝ) (fun i ↦ i ∈ S)).map_eq]
    have hvol :
        @volume ((↥S → ℝ) × ({ i : Fin 5 // i ∉ S } → ℝ))
            (@Measure.prod.measureSpace (↥S → ℝ) ({ i : Fin 5 // i ∉ S } → ℝ)
              (@MeasureSpace.pi (↥S)
                (Subtype.fintype (fun i : Fin 5 ↦ i ∈ S))
                (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))
              MeasureSpace.pi) =
          @volume ((↥S → ℝ) × ({ i : Fin 5 // i ∉ S } → ℝ))
            (@Measure.prod.measureSpace (↥S → ℝ) ({ i : Fin 5 // i ∉ S } → ℝ)
              (@MeasureSpace.pi (↥S)
                (Finset.Subtype.fintype S)
                (fun _ ↦ ℝ) (fun _ ↦ Real.measureSpace))
              MeasureSpace.pi) :=
      splitProductVolumeEqFinsetSubtypeVolume S
    exact congrArg (fun μ : Measure ((↥S → ℝ) × ({ i : Fin 5 // i ∉ S } → ℝ)) ↦ μ (A ×ˢ B)) hvol
  have hA_volume :
      volume.real A =
        (1 - ((S.card : ℝ) + 1) * simplexShrunkMargin) ^ S.card /
          (Nat.factorial S.card : ℝ) := by
    -- Proof comment: the shifted-simplex formula on the `S`-subtype gives the positive-block
    -- factor after rewriting its cardinality as `S.card`.
    calc
      volume.real A =
          (1 - simplexShrunkMargin -
              (Fintype.card ({i : Fin 5 // i ∈ S}) : ℝ) * simplexShrunkMargin) ^
              Fintype.card ({i : Fin 5 // i ∈ S}) /
            (Nat.factorial (Fintype.card ({i : Fin 5 // i ∈ S})) : ℝ) := by
              simpa [A] using
                (shiftedPositiveSimplexReal_eq_pow_div_factorial
                  ({i : Fin 5 // i ∈ S}) simplexShrunkMargin (1 - simplexShrunkMargin)
                  hmargin_nonneg hA_threshold)
      _ =
          (1 - ((S.card : ℝ) + 1) * simplexShrunkMargin) ^ S.card /
            (Nat.factorial S.card : ℝ) := by
              rw [card_subtype_mem_eq_card]
              congr 2
              ring_nf
  have hB_volume :
      volume.real B =
        (1 - (((5 - S.card : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - S.card) /
          (Nat.factorial (5 - S.card) : ℝ) := by
    -- Proof comment: negate the complementary block once, then apply the same shifted-simplex
    -- volume theorem on the complement subtype.
    calc
      volume.real B =
          volume.real
            {y : {i : Fin 5 // i ∉ S} → ℝ |
              (∀ i, simplexShrunkMargin ≤ y i) ∧ ∑ i, y i ≤ 1 - simplexShrunkMargin} := by
                simpa [B] using
                  (negShiftedPositiveSimplexReal_eq
                    ({i : Fin 5 // i ∉ S}) simplexShrunkMargin (1 - simplexShrunkMargin))
      _ =
          (1 - simplexShrunkMargin -
              (Fintype.card ({i : Fin 5 // i ∉ S}) : ℝ) * simplexShrunkMargin) ^
              Fintype.card ({i : Fin 5 // i ∉ S}) /
            (Nat.factorial (Fintype.card ({i : Fin 5 // i ∉ S})) : ℝ) := by
              exact shiftedPositiveSimplexReal_eq_pow_div_factorial
                ({i : Fin 5 // i ∉ S}) simplexShrunkMargin (1 - simplexShrunkMargin)
                hmargin_nonneg hB_threshold
      _ =
          (1 - (((5 - S.card : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - S.card) /
            (Nat.factorial (5 - S.card) : ℝ) := by
              rw [card_subtype_notMem_eq_card_compl]
              congr 2
              ring_nf
  -- Proof comment: transport volume through the split equivalence once, then multiply the two
  -- block volumes.
  calc
    volume.real (simplexShrunkSignCell S) = volume.real (e ⁻¹' (A ×ˢ B)) := by
      rw [hpreimage]
    _ = (volume.map e).real (A ×ˢ B) := by
          rw [MeasureTheory.map_measureReal_apply e.measurable (hA_meas.prod hB_meas)]
    _ = volume.real (A ×ˢ B) := by
          rw [Measure.real_def, Measure.real_def, hmap_apply]
    _ = volume.real A * volume.real B := by
          rw [MeasureTheory.Measure.volume_eq_prod]
          simpa using (MeasureTheory.measureReal_prod_prod (μ := volume) (ν := volume) A B)
    _ =
        ((1 - ((S.card : ℝ) + 1) * simplexShrunkMargin) ^ S.card /
            (Nat.factorial S.card : ℝ)) *
          ((1 - (((5 - S.card : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - S.card) /
            (Nat.factorial (5 - S.card) : ℝ)) := by
          rw [hA_volume, hB_volume]

/-- Helper for Exercise 13.1.5: regroup the sign-cell volume sum by the cardinality of the sign
set. -/
private lemma simplexShrunkSignCellVolume_sumByCard :
    ∑ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 5))),
        volume.real (simplexShrunkSignCell S) =
      ∑ k ∈ Finset.range 6,
        (Nat.choose 5 k : ℝ) *
          (((1 - ((k : ℝ) + 1) * simplexShrunkMargin) ^ k / (Nat.factorial k : ℝ)) *
            ((1 - (((5 - k : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - k) /
              (Nat.factorial (5 - k) : ℝ))) := by
  let f : ℕ → ℝ := fun k ↦
    ((1 - ((k : ℝ) + 1) * simplexShrunkMargin) ^ k / (Nat.factorial k : ℝ)) *
      ((1 - (((5 - k : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - k) /
        (Nat.factorial (5 - k) : ℝ))
  -- Proof comment: the explicit cell formula depends only on `S.card`, so the powerset sum
  -- collapses to the standard binomial count of subsets of each size.
  calc
    ∑ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 5))),
        volume.real (simplexShrunkSignCell S) =
      ∑ S ∈ (Finset.univ.powerset : Finset (Finset (Fin 5))), f S.card := by
        refine Finset.sum_congr rfl ?_
        intro T hT
        simpa [f] using (volumeReal_simplexShrunkSignCell T)
    _ =
      ∑ k ∈ Finset.range 6, (Nat.choose 5 k : ℝ) * f k := by
        simpa [f, Finset.card_univ, nsmul_eq_mul] using
          (Finset.sum_powerset_apply_card (α := ℝ) (β := Fin 5) f
            (x := (Finset.univ : Finset (Fin 5))))

/-- Helper for Exercise 13.1.5: the simplex translate union has real volume larger than the
selection threshold needed to beat the one-member upper bound. -/
private lemma simplexTranslateFamilyUnionLowerBound :
    (1 / 120 : ℝ) <
      ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) * volume.real (⋃₀ simplexTranslateFamily) := by
  let s : Finset (Finset (Fin 5)) := Finset.univ.powerset
  have hs_disj : PairwiseDisjoint (↑s) simplexShrunkSignCell := by
    simpa [s] using simplexShrunkSignCell_pairwiseDisjoint
  have hs_subset : (⋃ T ∈ s, simplexShrunkSignCell T) ⊆ ⋃₀ simplexTranslateFamily := by
    -- Proof comment: every sign cell already sits in the translate union, so the finite cell
    -- union is a measurable lower bound for the whole family union.
    intro z hz
    simp only [Set.mem_iUnion] at hz
    rcases hz with ⟨T, hT, hzT⟩
    exact simplexShrunkSignCell_subset_sUnion_family T hzT
  have hs_fin :
      ∀ T ∈ s, volume (simplexShrunkSignCell T) ≠ ⊤ := by
    -- Proof comment: each cell is contained in the finite-measure family union.
    intro T hT
    exact ne_top_of_le_ne_top simplexTranslateFamilySpec.2.ne
      (measure_mono (simplexShrunkSignCell_subset_sUnion_family T))
  have hs_union :
      volume.real (⋃ T ∈ s, simplexShrunkSignCell T) =
        ∑ T ∈ s, volume.real (simplexShrunkSignCell T) := by
    -- Proof comment: the 32 sign cells are pairwise disjoint and measurable, so finite additivity
    -- turns their union volume into a finite sum.
    exact MeasureTheory.measureReal_biUnion_finset (μ := volume) hs_disj
      (fun T hT ↦ simplexShrunkSignCell_measurableSet T) hs_fin
  have hs_sum_le :
      ∑ T ∈ s, volume.real (simplexShrunkSignCell T) ≤ volume.real (⋃₀ simplexTranslateFamily) := by
    rw [← hs_union]
    exact measureReal_mono hs_subset simplexTranslateFamilySpec.2.ne
  have hfactor_nonneg : 0 ≤ ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) := by
    positivity
  have hs_numeric :
      (1 / 120 : ℝ) <
        ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) *
          (∑ T ∈ s, volume.real (simplexShrunkSignCell T)) := by
    -- Proof comment: after grouping by subset cardinality, the remaining inequality is a finite
    -- rational computation in dimension five.
    rw [simplexShrunkSignCellVolume_sumByCard]
    have hvalue :
        ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) *
            ∑ x ∈ Finset.range 6,
              (Nat.choose 5 x : ℝ) *
                (((1 - ((x : ℝ) + 1) * simplexShrunkMargin) ^ x /
                      (Nat.factorial x : ℝ)) *
                  ((1 - (((5 - x : ℕ) : ℝ) + 1) * simplexShrunkMargin) ^ (5 - x) /
                    (Nat.factorial (5 - x) : ℝ))) =
          (60785053682062220274641 : ℝ) / 7290000000000000000000000 := by
      have hchoose2 : Nat.choose 5 2 = 10 := by decide
      have hchoose3 : Nat.choose 5 3 = 10 := by decide
      have hfact3 : Nat.factorial 3 = 6 := by decide
      have hfact4 : Nat.factorial 4 = 24 := by decide
      have hfact5 : Nat.factorial 5 = 120 := by decide
      norm_num [s, simplexShrunkMargin, Finset.sum_range_succ]
      rw [hchoose2, hchoose3, hfact3, hfact4, hfact5]
      norm_num
    rw [hvalue]
    norm_num
  calc
    (1 / 120 : ℝ) <
        ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) *
          (∑ T ∈ s, volume.real (simplexShrunkSignCell T)) := hs_numeric
    _ ≤ ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) * volume.real (⋃₀ simplexTranslateFamily) := by
          gcongr

/-- Exercise 13.1.5: a five-dimensional simplex already gives a counterexample to the printed
finite-disjoint-selection claim within a common-model family, so the printed first sentence is
itself false without an extra symmetry hypothesis on the common model. This is the diagnostic
common-model counterexample companion to `exercise_13_1_5`. -/
theorem simplex_common_model_counterexample_to_large_selection :
    ∃ (C : Set (Fin 5 → ℝ)) (𝒰 : Set (Set (Fin 5 → ℝ))),
      IsAsymmetricCommonHomotheticModel C 𝒰 ∧
      HasFiniteUnionMeasure 𝒰 ∧
      ¬ HasLargeMeasureSelection 𝒰 := by
  refine ⟨standardOpenSimplexFive, simplexTranslateFamily, simplexTranslateFamilySpec.1,
    simplexTranslateFamilySpec.2, ?_⟩
  intro hlarge
  rcases hlarge (1 / 30 : ℝ) (by norm_num) with ⟨s, hs_subset, hs_disj, hs_large⟩
  have hs_pairwise : (↑s : Set (Set (Fin 5 → ℝ))).PairwiseDisjoint id := by
    intro U hU V hV hUV
    exact hs_disj hU hV hUV
  have hs_upper :
      s.sum (fun U ↦ volume.real U) ≤ (1 / 120 : ℝ) :=
    simplexTranslateFamilySelectionBound s hs_subset hs_pairwise
  have hthreshold :
      (1 / 120 : ℝ) <
        ((1 - (1 / 30 : ℝ)) / (3 : ℝ) ^ 5) * volume.real (⋃₀ simplexTranslateFamily) :=
    simplexTranslateFamilyUnionLowerBound
  have hs_lower : (1 / 120 : ℝ) < s.sum (fun U ↦ volume.real U) :=
    lt_trans hthreshold hs_large
  exact (not_lt_of_ge hs_upper) hs_lower
