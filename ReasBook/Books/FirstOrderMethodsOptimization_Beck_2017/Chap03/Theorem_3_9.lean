/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_8
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_10

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open Filter
open scoped Topology

section

variable {E : Type u} {ι : Type v}
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [Finite ι] [Nonempty ι]

/- This item is `source-facing` in the chapter directional-derivative API. The owner
notions are `has_directional_derivative_at` and `directional_derivative` from Definition 3.8. The
active-index collection is auxiliary derived data, so this file keeps it inline in the theorem
statement instead of introducing a parallel public wrapper around the canonical active-index
subtype `{i : ι // f i x = ⨆ j : ι, f j x}`. The source-facing theorem below uses the textbook
proper/`effective_domain` assumptions, while the more general `finite_domain` formulation is kept
as a reusable companion helper. -/
recall has_directional_derivative_at
recall directional_derivative
recall effective_domain
recall finite_domain

-- Semantic recall note: no upstream mathlib theorem for this extended-real active-index max rule
-- surfaced in semantic search. The source proof uses the convergence identity
-- `t * ((fᵢ (x + t d) - fᵢ x) / t) + fᵢ x → fᵢ x`, so the formal statement records the needed
-- finite real-valued directional-derivative witnesses explicitly and keeps the `finite_domain`
-- variant as a companion generalization.

/-- Helper for Theorem 3.9: a branch with a finite directional derivative at an interior finite
domain point is right-continuous along the ray `x + t • d` as `t → 0⁺`. -/
private lemma branch_tendsto_right_of_has_directional_derivative_at
    {g : E → EReal} {x d : E}
    (hx : x ∈ interior (finite_domain g))
    (hdir : ∃ ℓ : ℝ, has_directional_derivative_at g x d (ℓ : EReal)) :
    Tendsto (fun t : ℝ ↦ g (x + t • d)) (𝓝[>] (0 : ℝ)) (𝓝 (g x)) := by
  rcases hdir with ⟨ℓ, hℓ⟩
  have hxfd : x ∈ finite_domain g := interior_subset hx
  have hdom : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ finite_domain g := by
    -- Small positive steps stay inside the finite domain because `x` is an interior point.
    have hcont : Tendsto (fun t : ℝ ↦ x + t • d) (𝓝 (0 : ℝ)) (𝓝 x) := by
      simpa using
        tendsto_const_nhds.add
          (((tendsto_id : Tendsto (fun t : ℝ ↦ t) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ))).smul_const d))
    have hinterior :
        ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), x + t • d ∈ interior (finite_domain g) := by
      exact (hcont.eventually <| isOpen_interior.mem_nhds hx).filter_mono nhdsWithin_le_nhds
    exact hinterior.mono fun t ht ↦ interior_subset ht
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hcoe :
      Tendsto (fun t : ℝ ↦ (t : EReal)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : EReal)) := by
    exact (continuous_coe_real_ereal.continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hmul :
      Tendsto
        (fun t : ℝ ↦ (t : EReal) * ((g (x + t • d) - g x) / (t : EReal)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((0 : EReal) * (ℓ : EReal))) := by
    -- Multiplying the quotient by `t` recovers the numerator in the limit.
    have hpair :
        Tendsto
          (fun t : ℝ ↦ ((t : EReal), (g (x + t • d) - g x) / (t : EReal)))
          (𝓝[>] (0 : ℝ))
          (𝓝 ((0 : EReal), (ℓ : EReal))) :=
      Filter.Tendsto.prodMk_nhds hcoe hℓ
    exact
      (EReal.continuousAt_mul (by simp) (by simp) (by simp) (by simp)).tendsto.comp hpair
  have hsum :
      Tendsto
        (fun t : ℝ ↦ (t : EReal) * ((g (x + t • d) - g x) / (t : EReal)) + g x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (((0 : EReal) * (ℓ : EReal)) + g x)) := by
    -- Adding back the base-point value gives the branch value itself.
    have hpair :
        Tendsto
          (fun t : ℝ ↦
            ((t : EReal) * ((g (x + t • d) - g x) / (t : EReal)), g x))
          (𝓝[>] (0 : ℝ))
          (𝓝 (((0 : EReal) * (ℓ : EReal)), g x)) :=
      Filter.Tendsto.prodMk_nhds hmul tendsto_const_nhds
    exact (EReal.continuousAt_add (by simp) (by simp)).tendsto.comp hpair
  have hsum' :
      Tendsto
        (fun t : ℝ ↦ (t : EReal) * ((g (x + t • d) - g x) / (t : EReal)) + g x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (g x)) := by
    simpa using hsum
  refine hsum'.congr' ?_
  filter_upwards [hdom, hpos] with t ht htp
  have hx0 : ((g x).toReal : EReal) = g x := by
    exact EReal.coe_toReal (mem_effective_domain.mp hxfd.1).ne hxfd.2
  have hxt : ((g (x + t • d)).toReal : EReal) = g (x + t • d) := by
    exact EReal.coe_toReal (mem_effective_domain.mp ht.1).ne ht.2
  have ht0 : (t : EReal) ≠ 0 := by
    exact_mod_cast ne_of_gt htp
  calc
    (t : EReal) * ((g (x + t • d) - g x) / (t : EReal)) + g x
        = (g (x + t • d) - g x) + g x := by
            rw [EReal.mul_div_cancel (by simp) (by simp) ht0]
    _ = (((g (x + t • d)).toReal : EReal) - ((g x).toReal : EReal)) + ((g x).toReal : EReal) := by
          simp [hxt, hx0]
    _ = ((g (x + t • d)).toReal : EReal) := by
          simpa using
            (EReal.sub_add_cancel :
              ((g (x + t • d)).toReal : EReal) - (g x).toReal + (g x).toReal =
                ((g (x + t • d)).toReal : EReal))
    _ = g (x + t • d) := hxt

/- Helper for Theorem 3.9: an inactive branch stays strictly below a chosen active branch for all
sufficiently small positive steps. -/
omit [Nonempty ι] in
private lemma eventually_inactive_lt_active_branch
    (f : ι → E → EReal) (x d : E)
    (hx : x ∈ ⋂ i : ι, interior (finite_domain (f i)))
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal))
    (i j : ι) (hi : f i x = ⨆ k : ι, f k x) (hj : f j x ≠ ⨆ k : ι, f k x) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f j (x + t • d) < f i (x + t • d) := by
  have hle : f j x ≤ f i x := by
    rw [hi]
    exact Finite.le_ciSup_of_le j le_rfl
  have hne : f j x ≠ f i x := by
    simpa [hi] using hj
  have hjlt : f j x < f i x := lt_of_le_of_ne hle hne
  obtain ⟨c, hcj, hci⟩ := EReal.exists_between_coe_real hjlt
  have hleft :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f j (x + t • d) < (c : EReal) := by
    -- The inactive branch stays below an intermediate real level near `x`.
    exact
      (branch_tendsto_right_of_has_directional_derivative_at
        ((Set.mem_iInter.mp hx) j) (hdir j)).eventually (Iio_mem_nhds hcj)
  have hright :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), (c : EReal) < f i (x + t • d) := by
    -- The active branch stays above the same intermediate level near `x`.
    exact
      (branch_tendsto_right_of_has_directional_derivative_at
        ((Set.mem_iInter.mp hx) i) (hdir i)).eventually (Ioi_mem_nhds hci)
  filter_upwards [hleft, hright] with t ht_left ht_right
  exact lt_trans ht_left ht_right

/-- Helper for Theorem 3.9: for positive `t`, the quotient of the active-branch supremum is the
supremum of the active branch quotients. -/
private lemma active_iSup_quotient_eq_iSup_quotients
    (f : ι → E → EReal) (x d : E) {t : ℝ} (ht : 0 < t) :
    (((iSup fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦ f i.1 (x + t • d)) -
          (⨆ j : ι, f j x)) / (t : EReal))
      =
      iSup
        (fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦
          (f i.1 (x + t • d) - f i.1 x) / (t : EReal)) := by
  classical
  let A : Type v := {i : ι // f i x = ⨆ j : ι, f j x}
  obtain ⟨i0, hi0⟩ : ∃ i : ι, f i x = ⨆ j : ι, f j x := exists_eq_ciSup_of_finite
  letI : Nonempty A := ⟨⟨i0, hi0⟩⟩
  have ht_nonneg : (0 : EReal) ≤ (t : EReal) := le_of_lt <| by exact_mod_cast ht
  refine le_antisymm ?_ ?_
  · -- An active branch attains the active supremum because the active index set is finite.
    obtain ⟨k, hk⟩ :
        ∃ k : A, f k.1 (x + t • d) = iSup fun j : A ↦ f j.1 (x + t • d) :=
      exists_eq_ciSup_of_finite
    calc
      (((iSup fun j : A ↦ f j.1 (x + t • d)) - (⨆ j : ι, f j x)) / (t : EReal))
          = (f k.1 (x + t • d) - f k.1 x) / (t : EReal) := by
              rw [← hk, k.property]
      _ ≤ iSup
            (fun i : A ↦ (f i.1 (x + t • d) - f i.1 x) / (t : EReal)) :=
        Finite.le_ciSup_of_le k le_rfl
  · -- Each active quotient is bounded by the quotient of the active supremum.
    refine iSup_le fun i : A ↦ ?_
    have hle :
        f i.1 (x + t • d) ≤ iSup (fun j : A ↦ f j.1 (x + t • d)) :=
      Finite.le_ciSup_of_le i le_rfl
    have hsub :
        f i.1 (x + t • d) - f i.1 x ≤
          iSup (fun j : A ↦ f j.1 (x + t • d)) - (⨆ j : ι, f j x) := by
      simpa [A, i.property] using (EReal.sub_le_sub hle le_rfl)
    exact EReal.div_le_div_right_of_nonneg ht_nonneg hsub

/-- Helper for Theorem 3.9: for small positive steps, the full branch supremum agrees with the
supremum over the active branches at `x`. -/
private lemma eventually_iSup_eq_iSup_active_branches
    (f : ι → E → EReal) (x d : E)
    (hx : x ∈ ⋂ i : ι, interior (finite_domain (f i)))
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
      (⨆ i : ι, f i (x + t • d)) =
        iSup (fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦ f i.1 (x + t • d)) := by
  classical
  let supx : EReal := ⨆ j : ι, f j x
  let A : Type v := {i : ι // f i x = supx}
  let activeSup : ℝ → EReal := fun t ↦ iSup fun i : A ↦ f i.1 (x + t • d)
  obtain ⟨i0, hi0⟩ : ∃ i : ι, f i x = supx := by
    simpa [supx] using (exists_eq_ciSup_of_finite : ∃ i : ι, f i x = ⨆ j : ι, f j x)
  have hbranch :
      ∀ j : ι, ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), f j (x + t • d) ≤ activeSup t := by
    intro j
    by_cases hj : f j x = supx
    · -- Active branches are always bounded by the active supremum.
      exact Filter.Eventually.of_forall fun t ↦
        Finite.le_ciSup_of_le (⟨j, hj⟩ : A) le_rfl
    · -- Inactive branches fall below the fixed active branch `i0` near `x`.
      exact
        (eventually_inactive_lt_active_branch f x d hx hdir i0 j hi0
          (by simpa [supx] using hj)).mono
          fun t ht ↦
            le_trans (le_of_lt ht) (Finite.le_ciSup_of_le (⟨i0, hi0⟩ : A) le_rfl)
  letI : Fintype ι := Fintype.ofFinite ι
  have hall :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        ∀ j ∈ (Finset.univ : Finset ι), f j (x + t • d) ≤ activeSup t := by
    rw [Filter.eventually_all_finset]
    intro j hj
    exact hbranch j
  refine hall.mono ?_
  intro t ht
  refine le_antisymm ?_ ?_
  · -- Every branch lies below the active supremum, so the full finite supremum does as well.
    rw [← Finset.sup_univ_eq_iSup]
    exact Finset.sup_le fun j hj ↦ ht j hj
  · -- Each active branch is one of the full family branches.
    simpa [activeSup, A] using
      (iSup_le fun i : A ↦ (Finite.le_ciSup_of_le i.1 le_rfl :
        f i.1 (x + t • d) ≤ ⨆ j : ι, f j (x + t • d)))

/-- Helper for Theorem 3.9: the finite-domain active-index max rule is the owner proof used by
both public wrappers in this file. -/
private theorem directional_derivative_iSup_eq_iSup_active_indices_core
    (f : ι → E → EReal) (x d : E)
    (hx : x ∈ ⋂ i : ι, interior (finite_domain (f i)))
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup
        (fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦
          directional_derivative (f i) x d) := by
  classical
  let supx : EReal := ⨆ j : ι, f j x
  let A : Type v := {i : ι // f i x = supx}
  obtain ⟨i0, hi0⟩ : ∃ i : ι, f i x = supx := by
    simpa [supx] using (exists_eq_ciSup_of_finite : ∃ i : ι, f i x = ⨆ j : ι, f j x)
  letI : Nonempty A := ⟨⟨i0, hi0⟩⟩
  letI : Fintype A := Fintype.ofFinite A
  have hactiveTendsto :
      Tendsto
        (fun t : ℝ ↦
          Finset.univ.sup
            (fun i : A ↦ (f i.1 (x + t • d) - f i.1 x) / (t : EReal)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (Finset.univ.sup fun i : A ↦ directional_derivative (f i.1) x d)) := by
    -- The active branch quotients converge branchwise to their directional derivatives.
    refine Tendsto.finset_sup_nhds_apply ?_
    intro i hi
    rcases hdir i.1 with ⟨ℓ, hℓ⟩
    simpa [directional_derivative_eq_of_has_directional_derivative_at hℓ] using hℓ
  have hactiveTendsto' :
      Tendsto
        (fun t : ℝ ↦
          iSup
            (fun i : A ↦
              (f i.1 (x + t • d) - f i.1 x) / (t : EReal)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (iSup fun i : A ↦ directional_derivative (f i.1) x d)) := by
    simpa [Finset.sup_univ_eq_iSup] using hactiveTendsto
  have hpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := by
    simpa using (self_mem_nhdsWithin : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))
  have hiSupEq :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (⨆ i : ι, f i (x + t • d)) = iSup (fun i : A ↦ f i.1 (x + t • d)) := by
    simpa [A, supx] using eventually_iSup_eq_iSup_active_branches f x d hx hdir
  have hquotEq :
      ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ),
        (((⨆ i : ι, f i (x + t • d)) - (⨆ j : ι, f j x)) / (t : EReal))
          =
        iSup
          (fun i : A ↦
            (f i.1 (x + t • d) - f i.1 x) / (t : EReal)) := by
    -- Rewrite the full quotient to the active quotient on a small right-neighborhood.
    filter_upwards [hiSupEq, hpos] with t ht_sup ht_pos
    rw [ht_sup]
    simpa [A, supx] using active_iSup_quotient_eq_iSup_quotients f x d ht_pos
  have hhas :
      has_directional_derivative_at (fun y ↦ ⨆ i : ι, f i y) x d
        (iSup fun i : A ↦ directional_derivative (f i.1) x d) := by
    -- The previous eventual equality transfers the active finite-sup limit to the full quotient.
    rw [has_directional_derivative_at]
    have hquotEq' :
        (fun t : ℝ ↦
          iSup
            (fun i : A ↦
              (f i.1 (x + t • d) - f i.1 x) / (t : EReal))) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun t : ℝ ↦ (((⨆ i : ι, f i (x + t • d)) - (⨆ j : ι, f j x)) / (t : EReal))) := by
      exact hquotEq.mono fun t ht ↦ ht.symm
    simpa [supx] using Tendsto.congr' hquotEq' hactiveTendsto'
  -- The directional derivative is the limit identified by the active family.
  simpa [A, supx] using directional_derivative_eq_of_has_directional_derivative_at hhas

/-- Theorem 3.9: for a finite nonempty family of proper extended-real-valued functions, at a point
`x ∈ ⋂ i, interior (effective_domain (f i))`, if every directional derivative at `x` along `d`
exists as a finite real value, then the directional derivative of the pointwise maximum is the
maximum of the directional derivatives over the active indices `I(x) = {i | fᵢ x = max_j fⱼ x}`. -/
theorem directional_derivative_iSup_eq_iSup_active_indices_of_proper
    (f : ι → E → EReal) (x d : E)
    (hproper : ∀ i : ι, IsProperExtendedRealFunction (f i))
    (hx : x ∈ ⋂ i : ι, interior (effective_domain (f i)))
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup
        (fun i : {i : ι // f i x = ⨆ j : ι, f j x} ↦
          directional_derivative (f i) x d) := by
  -- Replace `effective_domain` by `finite_domain` using properness, then invoke the core theorem.
  have hxFinite : x ∈ ⋂ i : ι, interior (finite_domain (f i)) := by
    rw [Set.mem_iInter]
    intro i
    have hx_i : x ∈ interior (effective_domain (f i)) := (Set.mem_iInter.mp hx) i
    simpa [finite_domain_eq_effective_domain (hproper i).ne_bot] using hx_i
  exact directional_derivative_iSup_eq_iSup_active_indices_core f x d hxFinite hdir

/-- Companion finite-domain generalization of the active-index max directional-derivative rule.
Under `hproper`, `finite_domain (f i)` agrees with `effective_domain (f i)`, so this specializes
to `directional_derivative_iSup_eq_iSup_active_indices_of_proper`. -/
theorem directional_derivative_iSup_eq_iSup_active_indices
    (f : ι → E → EReal) (x d : E)
    (hx : x ∈ ⋂ i : ι, interior (finite_domain (f i)))
    (hdir : ∀ i : ι, ∃ ℓ : ℝ, has_directional_derivative_at (f i) x d (ℓ : EReal)) :
    directional_derivative (fun y ↦ ⨆ i : ι, f i y) x d =
      iSup
        (fun i :
          {i : ι // f i x = ⨆ j : ι, f j x} ↦
          directional_derivative (f i) x d) := by
  -- This public theorem is exactly the finite-domain core theorem.
  exact directional_derivative_iSup_eq_iSup_active_indices_core f x d hx hdir

end
