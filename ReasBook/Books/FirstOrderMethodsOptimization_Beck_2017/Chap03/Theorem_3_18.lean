/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_16
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_1
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_6

-- Declarations for this item will be appended below by the statement pipeline.

open Bornology
open scoped BigOperators Pointwise

universe u v

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type v} [Fintype ι]

/- Theorem 3.18 is `source-facing` in the chapter subdifferential API. The owner notions
`effective_domain`, `is_convex_function`, `subdifferential`, and `intrinsicInterior ℝ` already
live upstream, so this file contributes only the relative-interior qualification for the existing
finite-sum rule. Under the qualification hypothesis, nonemptiness of every effective domain is
already forced, so the only primitive codomain restriction in the main theorem is that no summand
takes the value `⊥`. A strong-dual reformulation is kept below only as a private bridge on the
same normed finite-dimensional ambient. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall intrinsicInterior

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Helper for Theorem 3.18: under pointwise `≠ ⊥` on a finite family, every finite partial sum
also avoids `⊥`. -/
private theorem finset_sum_ne_bot_of_forall_neBot
    (f : ι → E → EReal) (s : Finset ι)
    (h_ne_bot : ∀ i ∈ s, ∀ y : E, f i y ≠ ⊥) (x : E) :
    s.sum (fun i ↦ f i x) ≠ ⊥ := by
  classical
  revert h_ne_bot
  refine Finset.induction_on s ?_ ?_
  · intro h_ne_bot
    simp
  · intro i s hi ih h_ne_bot
    have hi_ne_bot : f i x ≠ ⊥ := h_ne_bot i (Finset.mem_insert_self i s) x
    have hs_ne_bot :
        s.sum (fun j ↦ f j x) ≠ ⊥ := by
      apply ih
      intro j hj y
      exact h_ne_bot j (Finset.mem_insert_of_mem hj) y
    -- Peel off the insert step and use the binary `≠ ⊥` criterion for `EReal` addition.
    simp [Finset.sum_insert, hi, hi_ne_bot, hs_ne_bot]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Helper for Theorem 3.18: under pointwise `≠ ⊥`, a finite pointwise sum is finite at `x` iff
each summand is finite at `x`. -/
private theorem mem_effectiveDomain_finset_sumOn_iff_forall
    (f : ι → E → EReal) (s : Finset ι)
    (h_ne_bot : ∀ i ∈ s, ∀ y : E, f i y ≠ ⊥) (x : E) :
    x ∈ effective_domain (fun y ↦ s.sum (fun i ↦ f i y)) ↔
      ∀ i ∈ s, x ∈ effective_domain (f i) := by
  classical
  revert h_ne_bot
  refine Finset.induction_on s ?_ ?_
  · intro h_ne_bot
    simp [effective_domain]
  · intro i s hi ih h_ne_bot
    have hi_ne_bot : f i x ≠ ⊥ := h_ne_bot i (Finset.mem_insert_self i s) x
    have hs_ne_bot :
        s.sum (fun j ↦ f j x) ≠ ⊥ :=
      finset_sum_ne_bot_of_forall_neBot f s
        (fun j hj y ↦ h_ne_bot j (Finset.mem_insert_of_mem hj) y) x
    constructor
    · intro hx
      have hx_insert : f i x + s.sum (fun j ↦ f j x) < ⊤ := by
        simpa [effective_domain, Finset.sum_insert, hi] using hx
      have hx_ne_top : f i x + s.sum (fun j ↦ f j x) ≠ ⊤ := by
        exact lt_top_iff_ne_top.mp hx_insert
      have hsplit :
          f i x ≠ ⊤ ∧ s.sum (fun j ↦ f j x) ≠ ⊤ :=
        (EReal.add_ne_top_iff_ne_top₂ hi_ne_bot hs_ne_bot).mp hx_ne_top
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · exact lt_top_iff_ne_top.mpr hsplit.1
      · exact
          (ih (fun k hk y ↦ h_ne_bot k (Finset.mem_insert_of_mem hk) y)).mp
            (lt_top_iff_ne_top.mpr hsplit.2) j hj'
    · intro hx
      have hix : f i x ≠ ⊤ :=
        lt_top_iff_ne_top.mp (hx i (Finset.mem_insert_self i s))
      have hsx :
          s.sum (fun j ↦ f j x) ≠ ⊤ := by
        apply lt_top_iff_ne_top.mp
        exact
          (ih (fun k hk y ↦ h_ne_bot k (Finset.mem_insert_of_mem hk) y)).mpr
            (fun j hj ↦ hx j (Finset.mem_insert_of_mem hj))
      -- Reassemble the insert case from the two finite summands.
      simpa [effective_domain, Finset.sum_insert, hi] using
        (lt_top_iff_ne_top.mpr <|
          (EReal.add_ne_top_iff_ne_top₂ hi_ne_bot hs_ne_bot).mpr ⟨hix, hsx⟩)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: under pointwise `≠ ⊥`, the effective domain of the finite pointwise
sum is the intersection of the individual effective domains. -/
private theorem effectiveDomain_fintype_sum_eq_iInter_of_forall_neBot
    (f : ι → E → EReal) (h_ne_bot : ∀ i, ∀ y : E, f i y ≠ ⊥) :
    effective_domain (fun y ↦ ∑ i, f i y) = ⋂ i, effective_domain (f i) := by
  classical
  ext x
  -- Specialize the finite-partial-sum domain characterization to `Finset.univ`.
  rw [Set.mem_iInter]
  simpa using
    mem_effectiveDomain_finset_sumOn_iff_forall
      f Finset.univ (fun i _ y ↦ h_ne_bot i y) x

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [Fintype ι] in
/-- Helper for Theorem 3.18: under pointwise `≠ ⊥` on a finite family, the effective domain of a
finite partial sum is the intersection of the individual effective domains. -/
private theorem effectiveDomain_finset_sumOn_eq_iInter_of_forall_neBot
    (f : ι → E → EReal) (s : Finset ι)
    (h_ne_bot : ∀ i ∈ s, ∀ y : E, f i y ≠ ⊥) :
    effective_domain (fun y ↦ s.sum (fun i ↦ f i y)) = ⋂ i ∈ s, effective_domain (f i) := by
  classical
  ext x
  -- Normalize finite-sum domain membership to the previously proved iff for partial sums.
  simpa [Set.mem_iInter] using
    mem_effectiveDomain_finset_sumOn_iff_forall f s h_ne_bot x

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: the subdifferential of the zero function is the singleton `{0}`. -/
private theorem subdifferential_zero_eq_singleton (x : E) :
    ∂ (fun _ : E ↦ (0 : EReal))(x) = ({0} : Set (Module.Dual ℝ E)) := by
  ext g
  rw [mem_subdifferential]
  change is_subgradient_at (fun _ : E ↦ ((0 : ℝ) : EReal)) x g ↔ g ∈ ({0} : Set (Module.Dual ℝ E))
  rw [is_subgradient_at_coe_iff]
  constructor
  · intro hg
    have hg_zero : g = 0 := by
      ext v
      have hv_le : g v ≤ 0 := by
        simpa using hg (x + v)
      have hv_ge : 0 ≤ g v := by
        have hneg : -g v ≤ 0 := by
          simpa [sub_eq_add_neg, map_neg] using hg (x - v)
        linarith
      exact le_antisymm hv_le hv_ge
    simp [hg_zero]
  · intro hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    intro y
    simp

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: membership in the intrinsic interior is stable under binary
intersection. -/
private theorem mem_intrinsicInterior_inter
    {S T : Set E} {x : E}
    (hxS : x ∈ intrinsicInterior ℝ S)
    (hxT : x ∈ intrinsicInterior ℝ T) :
    x ∈ intrinsicInterior ℝ (S ∩ T) := by
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hxS with
    ⟨_, εS, hεS, hS⟩
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hxT with
    ⟨_, εT, hεT, hT⟩
  -- Put both intrinsic-interior neighborhoods under one common radius.
  refine (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).2 ?_
  refine ⟨subset_affineSpan ℝ (S ∩ T) ⟨intrinsicInterior_subset hxS, intrinsicInterior_subset hxT⟩,
    min εS εT, lt_min hεS hεT, ?_⟩
  intro y hy
  have hySaff : y ∈ affineSpan ℝ S := by
    exact affineSpan_mono ℝ (fun _ hz ↦ hz.1) hy.2
  have hyTaff : y ∈ affineSpan ℝ T := by
    exact affineSpan_mono ℝ (fun _ hz ↦ hz.2) hy.2
  refine ⟨?_, ?_⟩
  · exact hS ⟨Metric.closedBall_subset_closedBall (min_le_left _ _) hy.1, hySaff⟩
  · exact hT ⟨Metric.closedBall_subset_closedBall (min_le_right _ _) hy.1, hyTaff⟩

omit [FiniteDimensional ℝ E] [Fintype ι] in
/-- Helper for Theorem 3.18: a point in the intrinsic interior of every member of a finite family
lies in the intrinsic interior of their finite intersection. -/
private theorem mem_intrinsicInterior_iInter_finset_of_forall
    (S : ι → Set E) (s : Finset ι) {x : E}
    (hx : ∀ i ∈ s, x ∈ intrinsicInterior ℝ (S i)) :
    x ∈ intrinsicInterior ℝ (⋂ i ∈ s, S i) := by
  classical
  revert hx
  refine Finset.induction_on s ?_ ?_
  · intro hx
    simp
  · intro i s hi ih hx
    have hx_i : x ∈ intrinsicInterior ℝ (S i) :=
      hx i (Finset.mem_insert_self i s)
    have hx_s : x ∈ intrinsicInterior ℝ (⋂ j ∈ s, S j) := by
      apply ih
      intro j hj
      exact hx j (Finset.mem_insert_of_mem hj)
    -- Rewrite the finite intersection as a binary intersection and apply the previous helper.
    simpa [hi, Set.mem_iInter] using mem_intrinsicInterior_inter hx_i hx_s

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: subtracting a finite linear functional does not change the effective
domain. -/
private theorem effectiveDomain_sub_pairing_eq
    (h : E → EReal) (η : Module.Dual ℝ E) :
    effective_domain (fun z ↦ h z - (η z : EReal)) = effective_domain h := by
  ext x
  rw [mem_effective_domain, mem_effective_domain]
  constructor
  · intro hx
    -- A finite linear term cannot turn `⊤` into a finite value.
    by_contra htop
    have htop' : h x = ⊤ := le_antisymm le_top (not_lt.mp htop)
    have hnotlt : ¬ h x - (η x : EReal) < ⊤ := by
      simp [htop', sub_eq_add_neg]
    exact hnotlt hx
  · intro hx
    by_cases hbot : h x = ⊥
    · -- If `h x = ⊥`, subtracting a finite value keeps the value below `⊤`.
      simp [hbot, sub_eq_add_neg]
    · have htop : h x ≠ ⊤ := (lt_top_iff_ne_top.mp hx)
      have hshift_ne_top : h x + (-(η x : EReal)) ≠ ⊤ := by
        exact (EReal.add_ne_top_iff_ne_top₂ hbot (by simp)).2 ⟨htop, by simp⟩
      -- Otherwise the shifted value stays finite because both summands avoid `⊤`.
      simpa [sub_eq_add_neg] using lt_top_iff_ne_top.mpr hshift_ne_top

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: subtracting a finite linear functional also leaves the relative-
interior qualification on the effective domain unchanged. -/
private theorem intrinsicInterior_effectiveDomain_sub_pairing_eq
    (h : E → EReal) (η : Module.Dual ℝ E) :
    intrinsicInterior ℝ (effective_domain (fun z ↦ h z - (η z : EReal))) =
      intrinsicInterior ℝ (effective_domain h) := by
  -- The intrinsic interior only sees the underlying effective-domain set.
  rw [effectiveDomain_sub_pairing_eq]

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: subtracting a finite linear pairing preserves the pointwise
absence of `⊥`. -/
private theorem sub_pairing_neBot
    (h : E → EReal) (η : Module.Dual ℝ E)
    (h_ne_bot : ∀ z : E, h z ≠ ⊥) :
    ∀ z : E, (fun y ↦ h y - (η y : EReal)) z ≠ ⊥ := by
  intro z
  -- Expand the subtraction once and use the binary `≠ ⊥` criterion for `EReal` addition.
  change h z + (-(η z : EReal)) ≠ ⊥
  intro hbot
  rcases EReal.add_eq_bot_iff.mp hbot with hh | hη
  · exact h_ne_bot z hh
  · exact EReal.coe_ne_top _ (EReal.neg_eq_bot_iff.mp hη)

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: subtracting a finite linear pairing preserves convexity when the
original function never takes the value `⊥`. -/
private theorem is_convex_function_sub_pairing
    (h : E → EReal) (η : Module.Dual ℝ E)
    (hconvex : is_convex_function h) (h_ne_bot : ∀ z : E, h z ≠ ⊥) :
    is_convex_function (fun z ↦ h z - (η z : EReal)) := by
  have hconvexToReal :
      ConvexOn ℝ (effective_domain h) (fun z ↦ (h z).toReal) :=
    convexOn_toReal_of_is_convex_function hconvex (fun z _ ↦ h_ne_bot z)
  have hpairConcave : ConcaveOn ℝ (effective_domain h) (fun z ↦ η z) := by
    -- A linear functional is concave as well as convex on every convex domain.
    simpa using LinearMap.concaveOn η hconvexToReal.1
  have hshiftConvexToReal :
      ConvexOn ℝ (effective_domain h) (fun z ↦ (h z).toReal - η z) := by
    -- Subtract the concave linear pairing from the convex finite restriction of `h`.
    simpa [Pi.sub_apply] using hconvexToReal.sub hpairConcave
  have hrewrite :
      Set.EqOn
        (fun z ↦ ((h z - (η z : EReal)).toReal))
        (fun z ↦ (h z).toReal - η z)
        (effective_domain h) := by
    intro z hz
    have hz_top : h z ≠ ⊤ := lt_top_iff_ne_top.mp hz
    -- Rewrite the shifted `toReal` value as the original finite value minus the pairing.
    simpa [sub_eq_add_neg] using
      (EReal.toReal_add hz_top (h_ne_bot z) (by simp) (by simp :
        (-(η z : EReal)) ≠ ⊥))
  have hshift_ne_bot :
      ∀ z ∈ effective_domain (fun z ↦ h z - (η z : EReal)),
        (fun y ↦ h y - (η y : EReal)) z ≠ ⊥ := by
    intro z hz
    exact sub_pairing_neBot h η h_ne_bot z
  -- Use the `toReal` bridge on the unchanged effective domain after the finite shift.
  refine
    (is_convex_function_iff_convexOn_toReal hshift_ne_bot).2 ?_
  simpa [effectiveDomain_sub_pairing_eq h η] using
    hshiftConvexToReal.congr hrewrite.symm

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: on effective-domain points, the shifted supporting inequality for
`h - η` is equivalent to the unshifted supporting inequality for the translated dual vector
`g + η`. -/
private theorem subgradientInequality_sub_pairing_iff
    (h : E → EReal) (η g : Module.Dual ℝ E) (x y : E)
    (hx : x ∈ effective_domain h) (hy : y ∈ effective_domain h) :
    h y - (η y : EReal) ≥ h x - (η x : EReal) + (g (y - x) : EReal) ↔
      h y ≥ h x + (((g + η) (y - x) : ℝ) : EReal) := by
  by_cases hx_bot : h x = ⊥
  · -- If the base-point value is `⊥`, both lower-support inequalities are automatic.
    simp [hx_bot]
  · have hx_top : h x ≠ ⊤ := lt_top_iff_ne_top.mp hx
    by_cases hy_bot : h y = ⊥
    · -- If the target value is `⊥`, both inequalities fail because the shifted right-hand side is
      -- finite once `h x` is finite.
      have hx_eq : h x = (((h x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hx_top hx_bot).symm
      rw [hx_eq]
      simp [hy_bot, sub_eq_add_neg]
    · have hy_top : h y ≠ ⊤ := lt_top_iff_ne_top.mp hy
      have hx_eq : h x = (((h x).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hx_top hx_bot).symm
      have hy_eq : h y = (((h y).toReal : ℝ) : EReal) :=
        (EReal.coe_toReal hy_top hy_bot).symm
      have hη_sub :
          η (y - x) = η y - η x := by
        -- Rewrite the displacement pairing using linearity of `η`.
        simp [sub_eq_add_neg]
      have hsum :
          (g + η) (y - x) = g (y - x) + η y - η x := by
        -- Expand the translated dual vector on the displacement `y - x`.
        calc
          (g + η) (y - x) = g (y - x) + η (y - x) := by simp
          _ = g (y - x) + η y - η x := by
            rw [hη_sub]
            ring
      have hreal :
          (h y).toReal - η y ≥ (h x).toReal - η x + g (y - x) ↔
            (h y).toReal ≥ (h x).toReal + (g + η) (y - x) := by
        -- The two real inequalities differ only by the identity for the translated pairing.
        constructor
        · intro hineq
          rw [hsum]
          linarith
        · intro hineq
          rw [hsum] at hineq
          linarith
      rw [hx_eq, hy_eq]
      exact_mod_cast hreal

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: subtracting a finite linear functional from the function transports
the subgradient by adding that functional back on the dual side. -/
private theorem mem_subdifferential_sub_pairing_iff
    (h : E → EReal) (η g : Module.Dual ℝ E) (x : E) :
    g ∈ ∂ (fun z ↦ h z - (η z : EReal))(x) ↔ g + η ∈ ∂ h(x) := by
  rw [mem_subdifferential, mem_subdifferential]
  rw [is_subgradient_at_iff_forall_mem_effective_domain,
    is_subgradient_at_iff_forall_mem_effective_domain]
  constructor
  · rintro ⟨hx, hg⟩
    refine ⟨?_, ?_⟩
    · -- The finite linear shift leaves the effective domain unchanged.
      simpa [effectiveDomain_sub_pairing_eq h η] using hx
    · intro y hy
      have hy_shift :
          y ∈ effective_domain (fun z ↦ h z - (η z : EReal)) := by
        simpa [effectiveDomain_sub_pairing_eq h η] using hy
      -- Rewrite the shifted supporting inequality into the owner-level inequality for `g + η`.
      exact
        (subgradientInequality_sub_pairing_iff
          h η g x y
          (by simpa [effectiveDomain_sub_pairing_eq h η] using hx)
          hy).1
          (hg y hy_shift)
  · rintro ⟨hx, hg⟩
    refine ⟨?_, ?_⟩
    · -- The same effective-domain identification closes the reverse implication.
      simpa [effectiveDomain_sub_pairing_eq h η] using hx
    · intro y hy
      have hy_unshifted : y ∈ effective_domain h := by
        simpa [effectiveDomain_sub_pairing_eq h η] using hy
      -- Apply the same bridge in reverse to recover the shifted inequality.
      exact
        (subgradientInequality_sub_pairing_iff h η g x y hx hy_unshifted).2
          (hg y hy_unshifted)

/-- Helper for Theorem 3.18: the binary zero-case value function used to split a zero
subgradient of `h₁ + h₂`. -/
private noncomputable def zeroCaseValue
    (h₁ h₂ : E → EReal) : E → EReal :=
  fun d ↦ sInf (Set.range (fun u : E ↦ h₁ u + h₂ (u + d)))

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: any feasible witness `(u, u + d)` puts `d` in the effective domain
of the zero-case value function. -/
private theorem mem_effectiveDomain_zeroCaseValue_of_mem_domains
    (h₁ h₂ : E → EReal)
    {u d : E} (hu₁ : u ∈ effective_domain h₁) (hu₂ : u + d ∈ effective_domain h₂) :
    d ∈ effective_domain (zeroCaseValue h₁ h₂) := by
  rw [mem_effective_domain]
  have hu₁_top : h₁ u ≠ ⊤ := lt_top_iff_ne_top.mp hu₁
  have hu₂_top : h₂ (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hu₂
  -- Insert the concrete feasible witness and note that its value is finite.
  by_cases hbot₁ : h₁ u = ⊥
  · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [hbot₁]
  · by_cases hbot₂ : h₂ (u + d) = ⊥
    · exact lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) <| by simp [hbot₂]
    · refine lt_of_le_of_lt (sInf_le ⟨u, rfl⟩) ?_
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.add_ne_top_iff_ne_top₂ hbot₁ hbot₂).mpr
            ⟨hu₁_top, hu₂_top⟩

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: if the left summand ever takes the value `⊥`, then the zero-case
value function is identically `⊥`. -/
private theorem zeroCaseValue_eq_bot_of_exists_eq_bot_left
    (h₁ h₂ : E → EReal) (hbot : ∃ u : E, h₁ u = ⊥) :
    zeroCaseValue h₁ h₂ = fun _ : E ↦ (⊥ : EReal) := by
  rcases hbot with ⟨u, hu⟩
  funext d
  apply le_antisymm
  · -- A single `⊥` witness on the left forces every fiber infimum to be `⊥`.
    simpa [zeroCaseValue, hu] using
      (sInf_le ⟨u, rfl⟩ : zeroCaseValue h₁ h₂ d ≤ h₁ u + h₂ (u + d))
  · exact (bot_le : (⊥ : EReal) ≤ zeroCaseValue h₁ h₂ d)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: if the right summand ever takes the value `⊥`, then the zero-case
value function is identically `⊥`. -/
private theorem zeroCaseValue_eq_bot_of_exists_eq_bot_right
    (h₁ h₂ : E → EReal) (hbot : ∃ v : E, h₂ v = ⊥) :
    zeroCaseValue h₁ h₂ = fun _ : E ↦ (⊥ : EReal) := by
  rcases hbot with ⟨v, hv⟩
  funext d
  apply le_antisymm
  · -- Choose the fiber point `u = v - d` so that the right summand evaluates at the `⊥` point.
    simpa [zeroCaseValue, hv, sub_eq_add_neg, add_assoc] using
      (sInf_le ⟨v - d, by abel⟩ :
        zeroCaseValue h₁ h₂ d ≤ h₁ (v - d) + h₂ ((v - d) + d))
  · exact (bot_le : (⊥ : EReal) ≤ zeroCaseValue h₁ h₂ d)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: when both summands never take `⊥`, membership in the effective domain
of the zero-case value function is exactly the existence of a feasible finite witness. -/
private theorem mem_effectiveDomain_zeroCaseValue_iff_exists
    (h₁ h₂ : E → EReal) (h_ne_bot₁ : ∀ y : E, h₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, h₂ y ≠ ⊥)
    {d : E} :
    d ∈ effective_domain (zeroCaseValue h₁ h₂) ↔
      ∃ u : E, u ∈ effective_domain h₁ ∧ u + d ∈ effective_domain h₂ := by
  constructor
  · intro hd
    rw [mem_effective_domain] at hd
    rcases exists_lt_of_csInf_lt (Set.range_nonempty (fun u : E ↦ h₁ u + h₂ (u + d))) hd with
      ⟨a, ⟨u, rfl⟩, hau⟩
    have hsum_ne_top : h₁ u + h₂ (u + d) ≠ ⊤ := lt_top_iff_ne_top.mp hau
    have hsplit :
        h₁ u ≠ ⊤ ∧ h₂ (u + d) ≠ ⊤ :=
      (EReal.add_ne_top_iff_ne_top₂ (h_ne_bot₁ u) (h_ne_bot₂ (u + d))).mp hsum_ne_top
    exact ⟨u, lt_top_iff_ne_top.mpr hsplit.1, lt_top_iff_ne_top.mpr hsplit.2⟩
  · rintro ⟨u, hu₁, hu₂⟩
    exact mem_effectiveDomain_zeroCaseValue_of_mem_domains h₁ h₂ hu₁ hu₂

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: the binary zero-case value function is convex because it is the
partial infimum of a jointly convex kernel. -/
private theorem zeroCaseValue_isConvex
    (h₁ h₂ : E → EReal) (h_ne_bot₁ : ∀ y : E, h₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, h₂ y ≠ ⊥)
    (hconvex₁ : is_convex_function h₁) (hconvex₂ : is_convex_function h₂) :
    is_convex_function (zeroCaseValue h₁ h₂) := by
  let K : E × E → EReal := fun p ↦ h₁ p.2 + h₂ (p.2 + p.1)
  have hSecond : is_convex_function (fun p : E × E ↦ h₁ p.2) := by
    -- The first kernel factor is just `h₁` pulled back along the second projection.
    simpa using
      is_convex_function_precompose_linearMap_add
        hconvex₁
        (LinearMap.snd ℝ E E)
        (0 : E)
  have hSum : is_convex_function (fun p : E × E ↦ h₂ (p.2 + p.1)) := by
    -- The second factor is `h₂` pulled back along the sum map `(d, u) ↦ u + d`.
    simpa [add_comm] using
      is_convex_function_precompose_linearMap_add
        hconvex₂
        (LinearMap.snd ℝ E E + LinearMap.fst ℝ E E)
        (0 : E)
  have hKernel : is_convex_function K := by
    -- Add the two jointly convex factors pointwise.
    simpa [K] using
      is_convex_function_pointwise_add
        hSecond hSum
        (fun p ↦ h_ne_bot₁ p.2)
        (fun p ↦ h_ne_bot₂ (p.2 + p.1))
  -- Partial minimization preserves convexity of the owner value function.
  simpa [zeroCaseValue, K] using
    partial_infimum_is_convex_function hKernel

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: at a zero subgradient point of `h₁ + h₂`, the zero-case value
function takes the exact primal value `h₁ x + h₂ x` at the origin. -/
private theorem zeroCaseValue_zero_eq_sumAtPoint
    (h₁ h₂ : E → EReal) (x : E)
    (hzero : (0 : Module.Dual ℝ E) ∈ ∂(h₁ + h₂)(x)) :
    zeroCaseValue h₁ h₂ (0 : E) = h₁ x + h₂ x := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hzero
  rcases hzero with ⟨hx_sum, hsupport⟩
  apply le_antisymm
  · -- The base point `u = x` is one feasible witness in the origin fiber.
    simpa [zeroCaseValue] using (sInf_le ⟨x, by simp⟩ :
      zeroCaseValue h₁ h₂ (0 : E) ≤ h₁ x + h₂ (x + 0))
  · refine le_sInf ?_
    rintro _ ⟨u, rfl⟩
    by_cases hu_top : h₁ u + h₂ u = ⊤
    · -- If the fiber value is `⊤`, the lower bound is automatic.
      simp [hu_top]
    · have hu_sum : u ∈ effective_domain (h₁ + h₂) :=
        lt_top_iff_ne_top.mpr hu_top
      -- The zero subgradient inequality lower-bounds every finite fiber value by the base value.
      simpa [Pi.add_apply] using hsupport u hu_sum

/-- Helper for Theorem 3.18: the common relative-interior qualification on the two effective
domains should transport to the origin for the zero-case value function. -/
private theorem zero_mem_intrinsicInterior_effectiveDomain_zeroCaseValue
    (h₁ h₂ : E → EReal)
    (hqual :
      (intrinsicInterior ℝ (effective_domain h₁) ∩
        intrinsicInterior ℝ (effective_domain h₂)).Nonempty) :
    (0 : E) ∈ intrinsicInterior ℝ (effective_domain (zeroCaseValue h₁ h₂)) := by
  by_cases hbot₁ : ∃ y : E, h₁ y = ⊥
  · -- A `⊥` value on the left collapses the value function to `⊥`, so the effective domain is
    -- all of `E`.
    simp [zeroCaseValue_eq_bot_of_exists_eq_bot_left h₁ h₂ hbot₁, effective_domain]
  by_cases hbot₂ : ∃ y : E, h₂ y = ⊥
  · -- The symmetric `⊥` case on the right is identical.
    simp [zeroCaseValue_eq_bot_of_exists_eq_bot_right h₁ h₂ hbot₂, effective_domain]
  -- Route correction: once both summands avoid `⊥`, the value-function domain is controlled by
  -- feasible pairs in the individual effective domains, so the relative-interior argument can run
  -- on translated product neighborhoods and the subtraction map.
  have h_ne_bot₁ : ∀ y : E, h₁ y ≠ ⊥ := by
    intro y hy
    exact hbot₁ ⟨y, hy⟩
  have h_ne_bot₂ : ∀ y : E, h₂ y ≠ ⊥ := by
    intro y hy
    exact hbot₂ ⟨y, hy⟩
  rcases hqual with ⟨x₀, hx₀₁, hx₀₂⟩
  have hxdom₁ : x₀ ∈ effective_domain h₁ := intrinsicInterior_subset hx₀₁
  have hxdom₂ : x₀ ∈ effective_domain h₂ := intrinsicInterior_subset hx₀₂
  let D : Set E := effective_domain (zeroCaseValue h₁ h₂)
  let P₁ : Submodule ℝ E := (affineSpan ℝ (effective_domain h₁)).direction
  let P₂ : Submodule ℝ E := (affineSpan ℝ (effective_domain h₂)).direction
  let U₁ : Set P₁ := {v : P₁ | x₀ + (v : E) ∈ effective_domain h₁}
  let U₂ : Set P₂ := {v : P₂ | x₀ + (v : E) ∈ effective_domain h₂}
  have hU₁_zero : (0 : P₁) ∈ interior U₁ := by
    -- Translate the relative interior of `effective_domain h₁` to an honest interior neighborhood
    -- at the origin in the direction space.
    simpa [U₁, P₁] using translatedEffectiveDomainZero_mem_interior h₁ x₀ hx₀₁
  have hU₂_zero : (0 : P₂) ∈ interior U₂ := by
    -- Apply the same translation argument to the second effective domain.
    simpa [U₂, P₂] using translatedEffectiveDomainZero_mem_interior h₂ x₀ hx₀₂
  let diffLinear : P₁ × P₂ →ₗ[ℝ] E :=
    { toFun := fun p ↦ (p.2 : E) - (p.1 : E)
      map_add' := by
        intro p q
        simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      map_smul' := by
        intro a p
        simp [sub_eq_add_neg] }
  let W : Submodule ℝ E := LinearMap.range diffLinear
  let diffToRange : P₁ × P₂ →ₗ[ℝ] W := diffLinear.rangeRestrict
  let U : Set (P₁ × P₂) := U₁ ×ˢ U₂
  have hU_zero : (0 : P₁ × P₂) ∈ interior U := by
    -- The product of the two translated neighborhoods is still an interior neighborhood of `0`.
    rw [show U = U₁ ×ˢ U₂ by rfl, interior_prod_eq]
    exact ⟨hU₁_zero, hU₂_zero⟩
  have hImage_subset :
      diffToRange '' U ⊆ ((↑) ⁻¹' D : Set W) := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    rcases hp with ⟨hp₁, hp₂⟩
    -- A pair of translated domain points yields a feasible witness for the fiber difference.
    refine
      mem_effectiveDomain_zeroCaseValue_of_mem_domains h₁ h₂
        (u := x₀ + (p.1 : E)) (d := (p.2 : E) - (p.1 : E)) ?_ ?_
    · simpa [U₁] using hp₁
    · simpa [U₂, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hp₂
  have hDiffOpen : IsOpenMap diffToRange :=
    diffToRange.isOpenMap_of_finiteDimensional (LinearMap.surjective_rangeRestrict diffLinear)
  let O : Set W := diffToRange '' interior U
  have hO_zero : (0 : W) ∈ O := by
    -- The open-map image contains the origin because the source neighborhood contains the zero pair.
    refine ⟨0, hU_zero, ?_⟩
    simp [diffToRange, diffLinear]
  have hO_open : IsOpen O := by
    -- The open image of the interior product neighborhood stays open in the range subspace.
    exact hDiffOpen _ isOpen_interior
  have hO_subset : O ⊆ ((↑) ⁻¹' D : Set W) := by
    intro w hw
    rcases hw with ⟨p, hp, rfl⟩
    exact hImage_subset ⟨p, interior_subset hp, rfl⟩
  have hW_zero : (0 : W) ∈ interior ((↑) ⁻¹' D : Set W) := by
    -- Move the open product neighborhood through the subtraction map and then enlarge to the full
    -- preimage of the value-function domain in the range space.
    exact hO_open.mem_nhds hO_zero |> mem_interior_iff_mem_nhds.2 |> interior_mono hO_subset
  have hpreimage_span_top : Submodule.span ℝ (((↑) ⁻¹' D : Set W)) = ⊤ := by
    -- The preimage already contains a nonempty open neighborhood of the origin, so its linear
    -- span is all of the range subspace.
    apply Submodule.eq_top_of_nonempty_interior'
    exact ⟨0, interior_mono (show (((↑) ⁻¹' D : Set W)) ⊆ (Submodule.span ℝ (((↑) ⁻¹' D : Set W)) : Set W) from
      Submodule.subset_span) hW_zero⟩
  have hDomain_subset_W : D ⊆ (W : Set E) := by
    intro d hd
    rcases (mem_effectiveDomain_zeroCaseValue_iff_exists h₁ h₂ h_ne_bot₁ h_ne_bot₂).1 hd with
      ⟨u, hu₁, hu₂⟩
    have hu₁_aff : u ∈ affineSpan ℝ (effective_domain h₁) :=
      subset_affineSpan ℝ (effective_domain h₁) hu₁
    have hx₀_aff₁ : x₀ ∈ affineSpan ℝ (effective_domain h₁) :=
      subset_affineSpan ℝ (effective_domain h₁) hxdom₁
    have hu₂_aff : u + d ∈ affineSpan ℝ (effective_domain h₂) :=
      subset_affineSpan ℝ (effective_domain h₂) hu₂
    have hx₀_aff₂ : x₀ ∈ affineSpan ℝ (effective_domain h₂) :=
      subset_affineSpan ℝ (effective_domain h₂) hxdom₂
    refine ⟨⟨⟨u - x₀, by
      simpa [P₁] using
        (affineSpan ℝ (effective_domain h₁)).vsub_mem_direction hu₁_aff hx₀_aff₁⟩,
      ⟨u + d - x₀, by
        simpa [P₂] using
          (affineSpan ℝ (effective_domain h₂)).vsub_mem_direction hu₂_aff hx₀_aff₂⟩⟩, ?_⟩
    -- The witness decomposition places `d` in the subtraction-map range.
    simp [diffLinear, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
  have himage_preimage :
      (Submodule.subtype W) '' (((↑) ⁻¹' D : Set W)) = D := by
    ext d
    constructor
    · rintro ⟨w, hw, rfl⟩
      simpa using hw
    · intro hd
      exact ⟨⟨d, hDomain_subset_W hd⟩, hd, rfl⟩
  have hspan_D : Submodule.span ℝ D = W := by
    -- Map the full linear span of the preimage through the subtype inclusion back into `E`.
    calc
      Submodule.span ℝ D =
          Submodule.map (Submodule.subtype W) (Submodule.span ℝ (((↑) ⁻¹' D : Set W))) := by
            rw [Submodule.map_span, himage_preimage]
      _ = Submodule.map (Submodule.subtype W) ⊤ := by rw [hpreimage_span_top]
      _ = W := by simp
  have hzero_mem_D : (0 : E) ∈ D := by
    -- The qualification witness itself produces the zero difference.
    simpa [D] using
      (mem_effectiveDomain_zeroCaseValue_of_mem_domains h₁ h₂ (u := x₀) (d := 0) hxdom₁
        (by simpa using hxdom₂))
  have hD_le : affineSpan ℝ D ≤ W.toAffineSubspace := by
    -- The domain already lies in the range subspace, so its affine hull does as well.
    simpa [hspan_D] using (affineSpan_le_toAffineSubspace_span (k := ℝ) (s := D))
  have hW_le : W.toAffineSubspace ≤ affineSpan ℝ D := by
    intro x hx
    have hvectorSpan_D :
        vectorSpan ℝ D = Submodule.span ℝ D := by
      simpa using
        (vectorSpan_eq_span_vsub_set_right (k := ℝ) (s := D) hzero_mem_D)
    have hvec : x ∈ vectorSpan ℝ D := by
      rw [hvectorSpan_D, hspan_D]
      simpa [Submodule.mem_toAffineSubspace] using hx
    have hzero_aff : (0 : E) ∈ affineSpan ℝ D := mem_affineSpan ℝ hzero_mem_D
    -- Because `0 ∈ D`, every vector in the span of `D` is also a point in its affine hull.
    simpa using
      vadd_mem_affineSpan_of_mem_affineSpan_of_mem_vectorSpan (s := D) hzero_aff hvec
  have hspan_D_aff : affineSpan ℝ D = W.toAffineSubspace :=
    le_antisymm hD_le hW_le
  -- Rewrite the intrinsic-interior ambient affine span as the range subspace and use the open
  -- neighborhood already constructed there.
  rw [mem_intrinsicInterior, hspan_D_aff]
  refine ⟨⟨(0 : E), by simp [Submodule.mem_toAffineSubspace]⟩, ?_, rfl⟩
  simpa [D, Submodule.mem_toAffineSubspace] using hW_zero

omit [FiniteDimensional ℝ E] in
/-- Helper for Theorem 3.18: any subgradient of the zero-case value function at the origin yields
split subgradients of the two original summands at `x`. -/
private theorem split_subgradients_of_mem_zeroCaseValue_subdifferential
    (h₁ h₂ : E → EReal) (x : E) (η : Module.Dual ℝ E)
    (h_ne_bot₁ : ∀ y : E, h₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, h₂ y ≠ ⊥)
    (hx₁ : x ∈ effective_domain h₁) (hx₂ : x ∈ effective_domain h₂)
    (hvalue : zeroCaseValue h₁ h₂ (0 : E) = h₁ x + h₂ x)
    (hη : η ∈ subdifferential (zeroCaseValue h₁ h₂) (0 : E)) :
    -η ∈ ∂ h₁(x) ∧ η ∈ ∂ h₂(x) := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hη
  rcases hη with ⟨hzero_dom, hη_support⟩
  let _ := hzero_dom
  have hx₁_top : h₁ x ≠ ⊤ := lt_top_iff_ne_top.mp hx₁
  have hx₂_top : h₂ x ≠ ⊤ := lt_top_iff_ne_top.mp hx₂
  have hx₁_eq : h₁ x = (((h₁ x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hx₁_top (h_ne_bot₁ x)).symm
  have hx₂_eq : h₂ x = (((h₂ x).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hx₂_top (h_ne_bot₂ x)).symm
  constructor
  · -- Test the value-function support inequality on the witness `u = y`, `d = x - y`.
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hx₁, ?_⟩
    intro y hy
    let d : E := x - y
    have hyx : y + d ∈ effective_domain h₂ := by
      simpa [d, sub_eq_add_neg, add_assoc] using hx₂
    have hd : d ∈ effective_domain (zeroCaseValue h₁ h₂) := by
      -- The pair `(y, x)` is feasible in the value-function fiber at `d = x - y`.
      simpa [d, sub_eq_add_neg, add_assoc] using
        (mem_effectiveDomain_zeroCaseValue_of_mem_domains
          h₁ h₂ hy hyx)
    have hlower :
        h₁ x + h₂ x + (η (d - 0) : EReal) ≤ zeroCaseValue h₁ h₂ d := by
      simpa [hvalue] using hη_support d hd
    have hupper : zeroCaseValue h₁ h₂ d ≤ h₁ y + h₂ x := by
      -- The same feasible pair gives an upper witness in the defining infimum.
      simpa [zeroCaseValue, d, sub_eq_add_neg, add_assoc] using
        (sInf_le ⟨y, rfl⟩ : zeroCaseValue h₁ h₂ d ≤ h₁ y + h₂ (y + d))
    have hcombined : h₁ x + h₂ x + (η (x - y) : EReal) ≤ h₁ y + h₂ x := by
      simpa [d] using hlower.trans hupper
    have hcancel :
        h₁ x + (η (x - y) : EReal) ≤ h₁ y := by
      have hshifted :
          h₁ x + (η (x - y) : EReal) + h₂ x ≤ h₁ y + h₂ x := by
        simpa [add_assoc, add_left_comm, add_comm] using hcombined
      have hrewritten :
          (h₁ x + (η (x - y) : EReal)) + (((h₂ x).toReal : ℝ) : EReal) ≤
            h₁ y + (((h₂ x).toReal : ℝ) : EReal) := by
        rw [hx₂_eq] at hshifted
        exact hshifted
      exact (EReal.addLECancellable_coe ((h₂ x).toReal)).add_le_add_iff_right.mp hrewritten
    -- Rewrite the linear term into the target subgradient orientation `(-η) (y - x)`.
    simpa [sub_eq_add_neg, map_neg, add_assoc, add_left_comm, add_comm] using hcancel
  · -- Test the value-function support inequality on the witness `u = x`, `d = y - x`.
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hx₂, ?_⟩
    intro y hy
    let d : E := y - x
    have hxy : x + d ∈ effective_domain h₂ := by
      simpa [d, sub_eq_add_neg, add_assoc] using hy
    have hd : d ∈ effective_domain (zeroCaseValue h₁ h₂) := by
      -- The pair `(x, y)` is feasible in the value-function fiber at `d = y - x`.
      simpa [d, sub_eq_add_neg, add_assoc] using
        (mem_effectiveDomain_zeroCaseValue_of_mem_domains
          h₁ h₂ hx₁ hxy)
    have hlower :
        h₁ x + h₂ x + (η (d - 0) : EReal) ≤ zeroCaseValue h₁ h₂ d := by
      simpa [hvalue] using hη_support d hd
    have hupper : zeroCaseValue h₁ h₂ d ≤ h₁ x + h₂ y := by
      -- The same feasible pair gives an upper witness in the defining infimum.
      simpa [zeroCaseValue, d, sub_eq_add_neg, add_assoc] using
        (sInf_le ⟨x, rfl⟩ : zeroCaseValue h₁ h₂ d ≤ h₁ x + h₂ (x + d))
    have hcombined : h₁ x + h₂ x + (η (y - x) : EReal) ≤ h₁ x + h₂ y := by
      simpa [d] using hlower.trans hupper
    have hcancel :
        h₂ x + (η (y - x) : EReal) ≤ h₂ y := by
      have hshifted :
          h₂ x + (η (y - x) : EReal) + h₁ x ≤ h₂ y + h₁ x := by
        simpa [add_assoc, add_left_comm, add_comm] using hcombined
      have hrewritten :
          (h₂ x + (η (y - x) : EReal)) + (((h₁ x).toReal : ℝ) : EReal) ≤
            h₂ y + (((h₁ x).toReal : ℝ) : EReal) := by
        rw [hx₁_eq] at hshifted
        exact hshifted
      exact (EReal.addLECancellable_coe ((h₁ x).toReal)).add_le_add_iff_right.mp hrewritten
    simpa [add_assoc, add_left_comm, add_comm] using hcancel

/-- Helper for Theorem 3.18: after shifting away the target subgradient, the remaining binary
blocker is the zero-subgradient decomposition theorem under the common relative-interior
qualification. -/
private theorem exists_split_subgradients_of_zero_mem_sum_underQualification
    (h₁ h₂ : E → EReal) (x : E)
    (h_ne_bot₁ : ∀ y : E, h₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, h₂ y ≠ ⊥)
    (hconvex₁ : is_convex_function h₁) (hconvex₂ : is_convex_function h₂)
    (hqual :
      (intrinsicInterior ℝ (effective_domain h₁) ∩
        intrinsicInterior ℝ (effective_domain h₂)).Nonempty)
    (hzero : (0 : Module.Dual ℝ E) ∈ ∂ (h₁ + h₂)(x)) :
    ∃ η : Module.Dual ℝ E, η ∈ ∂ h₁(x) ∧ -η ∈ ∂ h₂(x) := by
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain] at hzero
  rcases hzero with ⟨hx_sum, hzero_support⟩
  let _ := hzero_support
  have hx_sum_ne_top : h₁ x + h₂ x ≠ ⊤ := lt_top_iff_ne_top.mp hx_sum
  have hx_split :
      h₁ x ≠ ⊤ ∧ h₂ x ≠ ⊤ :=
    (EReal.add_ne_top_iff_ne_top₂ (h_ne_bot₁ x) (h_ne_bot₂ x)).mp hx_sum_ne_top
  have hx₁ : x ∈ effective_domain h₁ :=
    lt_top_iff_ne_top.mpr hx_split.1
  have hx₂ : x ∈ effective_domain h₂ :=
    lt_top_iff_ne_top.mpr hx_split.2
  have hψ_convex :
      is_convex_function (zeroCaseValue h₁ h₂) :=
    zeroCaseValue_isConvex
      h₁ h₂ h_ne_bot₁ h_ne_bot₂ hconvex₁ hconvex₂
  have hψ_zero :
      zeroCaseValue h₁ h₂ (0 : E) = h₁ x + h₂ x :=
    zeroCaseValue_zero_eq_sumAtPoint
      h₁ h₂ x
      (by
        rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
        exact ⟨hx_sum, hzero_support⟩)
  have hψ_ri :
      (0 : E) ∈ intrinsicInterior ℝ (effective_domain (zeroCaseValue h₁ h₂)) :=
    zero_mem_intrinsicInterior_effectiveDomain_zeroCaseValue
      h₁ h₂ hqual
  rcases subdifferential_nonempty_at_relativeInterior_point
      (zeroCaseValue h₁ h₂) (0 : E) hψ_convex hψ_ri with
    ⟨η, hη⟩
  have hsplit :
      -η ∈ ∂ h₁(x) ∧ η ∈ ∂ h₂(x) :=
    split_subgradients_of_mem_zeroCaseValue_subdifferential
      h₁ h₂ x η h_ne_bot₁ h_ne_bot₂ hx₁ hx₂ hψ_zero hη
  rcases hsplit with ⟨hminusη, hη₂⟩
  -- Package the split witness with the orientation expected by the binary sum rule.
  refine ⟨-η, ?_, ?_⟩
  · simpa using hminusη
  · simpa using hη₂

/-- Helper for Theorem 3.18: once the zero-subgradient owner theorem is available, any subgradient
of the binary sum splits under the common relative-interior qualification. -/
private theorem mem_sum_subdifferential_of_mem_subdifferential_add_underQualification
    (f₁ f₂ : E → EReal) (x : E) (g : Module.Dual ℝ E)
    (h_ne_bot₁ : ∀ y : E, f₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, f₂ y ≠ ⊥)
    (hconvex₁ : is_convex_function f₁) (hconvex₂ : is_convex_function f₂)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f₁) ∩
        intrinsicInterior ℝ (effective_domain f₂)).Nonempty)
    (hg : g ∈ ∂ (f₁ + f₂)(x)) :
    g ∈ ∂ f₁(x) + ∂ f₂(x) := by
  have hshift_ne_bot₁ : ∀ y : E, (fun z ↦ f₁ z - (g z : EReal)) y ≠ ⊥ := by
    -- The everywhere-finite pairing cannot create a new `⊥` value.
    exact sub_pairing_neBot f₁ g h_ne_bot₁
  have hshift_convex₁ : is_convex_function (fun z ↦ f₁ z - (g z : EReal)) := by
    -- Rewrite convexity through the finite-valued `toReal` bridge before applying the linear shift.
    exact is_convex_function_sub_pairing f₁ g hconvex₁ h_ne_bot₁
  have hqual_shift :
      (intrinsicInterior ℝ (effective_domain (fun z ↦ f₁ z - (g z : EReal))) ∩
        intrinsicInterior ℝ (effective_domain f₂)).Nonempty := by
    simpa [intrinsicInterior_effectiveDomain_sub_pairing_eq f₁ g] using hqual
  have hzero :
      (0 : Module.Dual ℝ E) ∈ ∂ ((fun z ↦ f₁ z - (g z : EReal)) + f₂)(x) := by
    have hshift_fun :
        (fun z ↦ f₁ z + f₂ z - (g z : EReal)) =
          ((fun z ↦ f₁ z - (g z : EReal)) + f₂) := by
      funext z
      simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
    have hshifted :
        (0 : Module.Dual ℝ E) ∈ ∂ (fun z ↦ (f₁ z + f₂ z) - (g z : EReal))(x) := by
      exact
        (mem_subdifferential_sub_pairing_iff
          (fun z ↦ f₁ z + f₂ z) g (0 : Module.Dual ℝ E) x).2
          (by simpa [Pi.add_apply] using hg)
    -- Fix the spelling of the shifted sum before invoking the zero-subgradient owner theorem.
    simpa [hshift_fun] using hshifted
  rcases exists_split_subgradients_of_zero_mem_sum_underQualification
      (fun z ↦ f₁ z - (g z : EReal)) f₂ x
      hshift_ne_bot₁ h_ne_bot₂ hshift_convex₁ hconvex₂ hqual_shift hzero with
    ⟨η, hη, hminusη⟩
  have hη_unshifted : η + g ∈ ∂ f₁(x) := by
    exact
      (mem_subdifferential_sub_pairing_iff f₁ g η x).1 hη
  -- Transport the shifted witness back and package the exact decomposition into the Minkowski sum.
  rw [Set.mem_add]
  refine ⟨η + g, hη_unshifted, -η, hminusη, ?_⟩
  ext v
  simp [add_comm, add_assoc]

/-- Helper for Theorem 3.18: the qualified exact two-function sum rule is the unique remaining
binary blocker for the finite-family argument. -/
private theorem subdifferential_add_eq_sum_subdifferential_of_nonempty_inter_intrinsicInterior
    (f₁ f₂ : E → EReal) (x : E)
    (h_ne_bot₁ : ∀ y : E, f₁ y ≠ ⊥) (h_ne_bot₂ : ∀ y : E, f₂ y ≠ ⊥)
    (hconvex₁ : is_convex_function f₁) (hconvex₂ : is_convex_function f₂)
    (hqual :
      (intrinsicInterior ℝ (effective_domain f₁) ∩
        intrinsicInterior ℝ (effective_domain f₂)).Nonempty) :
    ∂ (f₁ + f₂)(x) = ∂ f₁(x) + ∂ f₂(x) := by
  -- Route correction: isolate the zero-subgradient decomposition as the only remaining owner
  -- theorem, then package the binary exact rule as the hard inclusion plus the weak sum rule.
  apply Set.Subset.antisymm
  · intro g hg
    exact
      mem_sum_subdifferential_of_mem_subdifferential_add_underQualification
        f₁ f₂ x g h_ne_bot₁ h_ne_bot₂ hconvex₁ hconvex₂ hqual hg
  · exact sum_subdifferential_subset_subdifferential_add f₁ f₂ x

omit [Fintype ι] in
/-- Helper for Theorem 3.18: once the binary qualified sum rule is available, the exact finite-sum
rule follows by Finset induction under a common intrinsic-interior qualification. -/
private theorem subdifferential_finset_sum_eq_sum_subdifferential_sumOn_of_nonempty_relativeInterior
    (f : ι → E → EReal) (x : E) (s : Finset ι)
    (h_ne_bot : ∀ i ∈ s, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i ∈ s, is_convex_function (f i))
    (hqual : (⋂ i ∈ s, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    ∂ (fun y ↦ s.sum (fun i ↦ f i y))(x) = s.sum (fun i ↦ ∂ (f i)(x)) := by
  classical
  revert h_ne_bot hconvex hqual
  refine Finset.induction_on s ?_ ?_
  · intro h_ne_bot hconvex hqual
    ext g
    simp [subdifferential_zero_eq_singleton x]
  · intro i s hi ih h_ne_bot hconvex hqual
    have h_ne_bot_i : ∀ y : E, f i y ≠ ⊥ := by
      intro y
      exact h_ne_bot i (Finset.mem_insert_self i s) y
    have h_ne_bot_s : ∀ j ∈ s, ∀ y : E, f j y ≠ ⊥ := by
      intro j hj y
      exact h_ne_bot j (Finset.mem_insert_of_mem hj) y
    have hconvex_i : is_convex_function (f i) := hconvex i (Finset.mem_insert_self i s)
    have hconvex_s : ∀ j ∈ s, is_convex_function (f j) := by
      intro j hj
      exact hconvex j (Finset.mem_insert_of_mem hj)
    rcases hqual with ⟨x₀, hx₀⟩
    have hx₀_all : ∀ j ∈ insert i s, x₀ ∈ intrinsicInterior ℝ (effective_domain (f j)) := by
      simpa [Set.mem_iInter] using hx₀
    have hx₀_tail :
        x₀ ∈ intrinsicInterior ℝ (effective_domain (fun y ↦ s.sum (fun j ↦ f j y))) := by
      have hx₀_inter :
          x₀ ∈ intrinsicInterior ℝ (⋂ j ∈ s, effective_domain (f j)) :=
        mem_intrinsicInterior_iInter_finset_of_forall
          (fun j ↦ effective_domain (f j)) s
          (fun j hj ↦ hx₀_all j (Finset.mem_insert_of_mem hj))
      simpa [effectiveDomain_finset_sumOn_eq_iInter_of_forall_neBot f s h_ne_bot_s]
        using hx₀_inter
    have hqual_pair :
        (intrinsicInterior ℝ (effective_domain (f i)) ∩
          intrinsicInterior ℝ
            (effective_domain (fun y ↦ s.sum (fun j ↦ f j y)))).Nonempty := by
      exact ⟨x₀, hx₀_all i (Finset.mem_insert_self i s), hx₀_tail⟩
    have htailEq :
        ∂ (fun y ↦ s.sum (fun j ↦ f j y))(x) = s.sum (fun j ↦ ∂ (f j)(x)) :=
      ih h_ne_bot_s hconvex_s
        (by
          refine ⟨x₀, ?_⟩
          rw [Set.mem_iInter]
          intro j
          rw [Set.mem_iInter]
          intro hj
          exact hx₀_all j (Finset.mem_insert_of_mem hj))
    have htailConvex :
        is_convex_function (fun y ↦ s.sum (fun j ↦ f j y)) := by
      simpa using
        is_convex_function_finset_nonneg_weighted_sum s hconvex_s h_ne_bot_s (fun _ ↦ 1)
    have htail_ne_bot :
        ∀ y : E, (fun z ↦ s.sum (fun j ↦ f j z)) y ≠ ⊥ := by
      intro y
      exact finset_sum_ne_bot_of_forall_neBot f s h_ne_bot_s y
    have hinsertSum :
        (fun y ↦ (insert i s).sum (fun j ↦ f j y)) =
          f i + fun y ↦ s.sum (fun j ↦ f j y) := by
      funext y
      simp [Finset.sum_insert, hi, Pi.add_apply]
    -- Reduce the insert step to the binary qualified rule and the induction hypothesis.
    calc
      subdifferential (fun y ↦ (insert i s).sum (fun j ↦ f j y)) x
          = subdifferential (f i + fun y ↦ s.sum (fun j ↦ f j y)) x := by
              rw [hinsertSum]
      _ = subdifferential (f i) x +
            subdifferential (fun y ↦ s.sum (fun j ↦ f j y)) x := by
            exact
              subdifferential_add_eq_sum_subdifferential_of_nonempty_inter_intrinsicInterior
                (f i) (fun y ↦ s.sum (fun j ↦ f j y)) x
                h_ne_bot_i htail_ne_bot hconvex_i htailConvex hqual_pair
      _ = subdifferential (f i) x + s.sum (fun j ↦ subdifferential (f j) x) := by
            rw [htailEq]
      _ = (insert i s).sum (fun j ↦ subdifferential (f j) x) := by
            simp [Finset.sum_insert, hi]

-- Proof sketch: the inclusion `⊇` is the weak sum rule obtained by summing subgradient
-- inequalities. For `⊆`, use Rockafellar's conjugate sum theorem under the qualification
-- `(⋂ i, ri(dom fᵢ)).Nonempty`, choose an optimal decomposition of a conjugate
-- subgradient of the
-- sum, and apply Fenchel--Young equality termwise to show that each component lies in the
-- corresponding subdifferential. The relative-interior qualification already implies every
-- `effective_domain (f i)` is nonempty, so only the no-`⊥` half of properness is primitive data.
/-- Theorem 3.18: if a finite family of convex extended-real-valued functions
never takes the value `-∞` and has nonempty intersection of the relative
interiors of its effective domains, then
`∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ (f i)(x)` at every point. The
relative-interior hypothesis is rendered by `intrinsicInterior ℝ`. -/
theorem subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
    (f : ι → E → EReal) (x : E)
    (h_ne_bot : ∀ i, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i, is_convex_function (f i))
    (hqual : (⋂ i, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    ∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ (f i)(x) := by
  classical
  -- Route correction: package the global theorem through the finite-partial-sum induction, so the
  -- only remaining missing ingredient is the qualified binary exact sum rule above.
  have hqual_univ : (⋂ i ∈ Finset.univ, intrinsicInterior ℝ (effective_domain (f i))).Nonempty := by
    rcases hqual with ⟨x₀, hx₀⟩
    refine ⟨x₀, ?_⟩
    simpa [Set.mem_iInter] using hx₀
  simpa using
    subdifferential_finset_sum_eq_sum_subdifferential_sumOn_of_nonempty_relativeInterior
      f x Finset.univ (fun i _ y ↦ h_ne_bot i y) (fun i _ ↦ hconvex i) hqual_univ

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type v} [Fintype ι]
variable {κ : Type*}

recall strongDualSubdifferential
recall strongDualSubdifferential_eq_image_subdifferential

omit [FiniteDimensional ℝ E] in
private theorem image_finset_sum
    (e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E) (s : Finset κ)
    (f : κ → Set (Module.Dual ℝ E)) :
    e '' s.sum f = s.sum (fun i ↦ e '' f i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · ext g
    simp
  · intro i s hi ih
    simp [Finset.sum_insert, hi, ih, Set.image_add]

-- Strong-dual reformulation of the source-facing finite-sum rule, used downstream.
theorem strongDualSubdifferential_finset_sum_eq_sum_of_nonempty_iInter_relativeInterior
    (f : ι → E → EReal) (x : E)
    (h_ne_bot : ∀ i, ∀ y : E, f i y ≠ ⊥)
    (hconvex : ∀ i, is_convex_function (f i))
    (hqual : (⋂ i, intrinsicInterior ℝ (effective_domain (f i))).Nonempty) :
    ∂ₛ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ₛ (f i)(x) := by
  let e : (Module.Dual ℝ E) ≃ₗ[ℝ] StrongDual ℝ E := LinearMap.toContinuousLinearMap
  have hsub :
      ∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, ∂ (f i)(x) :=
    subdifferential_finset_sum_eq_sum_subdifferential_of_nonempty_iInter_relativeInterior
      f x h_ne_bot hconvex hqual
  have himage :
      e '' ∂ (fun y ↦ ∑ i, f i y)(x) = ∑ i, e '' ∂ (f i)(x) := by
    rw [hsub]
    simpa using image_finset_sum e Finset.univ (fun i ↦ ∂ (f i)(x))
  have hstrong : ∀ i, e '' ∂ (f i)(x) = ∂ₛ (f i)(x) := by
    intro i
    simpa [e] using (strongDualSubdifferential_eq_image_subdifferential (f i) x).symm
  calc
    strongDualSubdifferential (fun y ↦ ∑ i, f i y) x =
        e '' subdifferential (fun y ↦ ∑ i, f i y) x :=
      strongDualSubdifferential_eq_image_subdifferential _ _
    _ = ∑ i, e '' ∂ (f i)(x) := himage
    _ = ∑ i, ∂ₛ (f i)(x) := by
      simp_rw [hstrong]

end
