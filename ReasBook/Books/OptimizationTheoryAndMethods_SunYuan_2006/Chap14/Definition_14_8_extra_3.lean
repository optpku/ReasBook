/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Definition_14_8_extra_2

noncomputable section

section

variable {n : ℕ}

open Filter
open scoped GeneralizedJacobian

local notation "Point" => EuclideanSpace ℝ (Fin n)
local notation "JacobianMap" => Point →L[ℝ] Point

/- The book's "strong Fréchet derivative at `x`" is the canonical mathlib predicate
`HasStrictFDerivAt F A x`, encoding `(F z - F y - A (z - y)) / ‖z - y‖ → 0` as
`(y, z) → (x, x)`. -/
#check HasStrictFDerivAt

/-- Helper for Chapter14 Definition 14.8-extra-3: a strong Fréchet derivative at `x` gives a
closed-ball Lipschitz neighborhood of `x`, hence `LocallyLipschitzAt F x`. -/
lemma locallyLipschitzAt_of_hasStrictFDerivAt
    {F : Point → Point} {A : JacobianMap} {x : Point}
    (h_strict : HasStrictFDerivAt F A x) :
    LocallyLipschitzAt F x := by
  -- First take the standard strict-derivative Lipschitz neighborhood from mathlib.
  rcases h_strict.exists_lipschitzOnWith with ⟨K, s, hs, hK⟩
  rcases Metric.mem_nhds_iff.mp hs with ⟨ε, hε, hεsub⟩
  refine locallyLipschitzAt_of_closedBall (K := K) ?_
  refine ⟨ε / 2, by linarith, ?_⟩
  -- Then shrink that neighborhood to a concrete closed ball centered at `x`.
  intro y hy z hz
  exact hK
    (hεsub <| Metric.closedBall_subset_ball (by linarith) hy)
    (hεsub <| Metric.closedBall_subset_ball (by linarith) hz)

/-- Helper for Chapter14 Definition 14.8-extra-3: strict differentiability packages the remainder
`z ↦ F z - A z` as a small Lipschitz perturbation on an open neighborhood of `x`. -/
lemma errorLipschitzOn_openNhd_of_hasStrictFDerivAt
    {F : Point → Point} {A : JacobianMap} {x : Point}
    (h_strict : HasStrictFDerivAt F A x)
    {δ : NNReal} (hδ : 0 < δ) :
    ∃ s : Set Point, x ∈ s ∧ IsOpen s ∧
      LipschitzOnWith δ (fun z : Point ↦ F z - A z) s := by
  -- Use the strict-derivative approximation interface instead of unfolding the little-o
  -- definition directly in the semismoothness proof.
  rcases h_strict.approximates_deriv_on_nhds (Or.inr hδ) with ⟨t, ht, happ⟩
  rcases mem_nhds_iff.mp ht with ⟨s, hs_subset, hs_open, hx_mem⟩
  have hLip : LipschitzOnWith δ (F - ⇑A) t := by
    simpa using happ.lipschitzOnWith
  refine ⟨s, hx_mem, hs_open, ?_⟩
  -- Restrict the approximation estimate to an open neighborhood of `x`.
  intro y hy z hz
  simpa [Pi.sub_apply] using hLip (hs_subset hy) (hs_subset hz)

/-- Helper for Chapter14 Definition 14.8-extra-3: if the remainder map `z ↦ F z - A z` is
`δ`-Lipschitz on an open neighborhood of `y`, then every operator in `generalizedJacobian F y`
lies in the operator closed ball `Metric.closedBall A δ`. -/
lemma generalizedJacobian_subset_closedBall_of_errorLipschitzOn
    {F : Point → Point} {A : JacobianMap} {y : Point} {δ : NNReal} {s : Set Point}
    (hs_open : IsOpen s) (hy : y ∈ s)
    (hLip : LipschitzOnWith δ (fun z : Point ↦ F z - A z) s) :
    generalizedJacobian F y ⊆ Metric.closedBall A (δ : ℝ) := by
  intro B hB
  rw [mem_generalizedJacobian_iff] at hB
  have hGeneratorSubset :
      {V : JacobianMap | ∃ xs : ℕ → Point,
          Tendsto xs atTop (nhds y) ∧
          (∀ i : ℕ, DifferentiableAt ℝ F (xs i)) ∧
          Tendsto (fun i : ℕ ↦ fderiv ℝ F (xs i)) atTop (nhds V)}
        ⊆ Metric.closedBall A (δ : ℝ) := by
    intro V hV
    rcases hV with ⟨xs, hxs, hdiff, hlim⟩
    have hs_event : ∀ᶠ i in atTop, xs i ∈ s := hxs (hs_open.mem_nhds hy)
    have hLip' : LipschitzOnWith δ (F - ⇑A) s := by
      convert hLip using 1 <;> funext z <;> rfl
    have hball_event :
        ∀ᶠ i in atTop, fderiv ℝ F (xs i) ∈ Metric.closedBall A (δ : ℝ) := by
      filter_upwards [hs_event] with i hsi
      have hs_nhds : s ∈ nhds (xs i) := hs_open.mem_nhds hsi
      have hnorm :
          ‖fderiv ℝ (F - ⇑A) (xs i)‖ ≤ (δ : ℝ) :=
        norm_fderiv_le_of_lipschitzOn ℝ hs_nhds hLip'
      have hderiv : HasFDerivAt (F - ⇑A) (fderiv ℝ F (xs i) - A) (xs i) := by
        simpa using (hdiff i).hasFDerivAt.sub A.hasFDerivAt
      have hEq :
          fderiv ℝ (F - ⇑A) (xs i) = fderiv ℝ F (xs i) - A :=
        hderiv.fderiv
      have hnorm' : ‖fderiv ℝ F (xs i) - A‖ ≤ (δ : ℝ) := by
        simpa [hEq] using hnorm
      simpa [Metric.mem_closedBall, dist_eq_norm] using hnorm'
    -- Pass the derivative bound to the generator limit.
    exact (Metric.isClosed_closedBall : IsClosed (Metric.closedBall A (δ : ℝ))).mem_of_tendsto hlim hball_event
  -- The generalized Jacobian is the convex hull of those generators, and closed balls are convex.
  exact (convexHull_min hGeneratorSubset (convex_closedBall A (δ : ℝ))) hB

/-- Helper for Chapter14 Definition 14.8-extra-3: strict differentiability at `x` forces the
semismooth linearization limit in every direction `h` to be `A h`. -/
lemma hasSemismoothLinearizationLimit_of_hasStrictFDerivAt
    {F : Point → Point} {A : JacobianMap} {x h : Point}
    (h_strict : HasStrictFDerivAt F A x) :
    hasSemismoothLinearizationLimit F x h (A h) := by
  rw [hasSemismoothLinearizationLimit_iff]
  refine Metric.tendsto_nhds.2 ?_
  intro ε hε
  let δ : NNReal := ⟨ε / (4 * (‖h‖ + 1)), by positivity⟩
  have hδ : 0 < δ := by
    change 0 < (δ : ℝ)
    dsimp [δ]
    exact div_pos hε (by positivity)
  obtain ⟨s, hx_mem, hs_open, hLip⟩ :=
    errorLipschitzOn_openNhd_of_hasStrictFDerivAt h_strict (δ := δ) hδ
  let proj : JacobianMap × Point × ℝ → Point × ℝ := fun p ↦ (p.2.1, p.2.2)
  have hpair :
      Tendsto proj (semismoothSelectionFilter F x h)
        (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    -- The semismooth selection filter refines the product filter through the projection `proj`.
    exact Filter.tendsto_comap.mono_left (by
      simpa [semismoothSelectionFilter, proj] using
        (inf_le_right :
          semismoothSelectionFilter F x h ≤
            comap proj (nhds h ×ˢ nhdsWithin (0 : ℝ) (Set.Ioi 0))))
  have hh' :
      Tendsto (fun p : JacobianMap × Point × ℝ ↦ p.2.1)
        (semismoothSelectionFilter F x h) (nhds h) := by
    have hfst : Tendsto (((fun q : Point × ℝ ↦ q.1) : Point × ℝ → Point) ∘ proj)
        (semismoothSelectionFilter F x h) (nhds h) :=
      tendsto_fst.comp hpair
    convert hfst using 1 <;> funext p <;> rfl
  have ht :
      Tendsto (fun p : JacobianMap × Point × ℝ ↦ p.2.2)
        (semismoothSelectionFilter F x h) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    have hsnd : Tendsto (((fun q : Point × ℝ ↦ q.2) : Point × ℝ → ℝ) ∘ proj)
        (semismoothSelectionFilter F x h) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
      tendsto_snd.comp hpair
    convert hsnd using 1 <;> funext p <;> rfl
  have ht0 :
      Tendsto (fun p : JacobianMap × Point × ℝ ↦ p.2.2)
        (semismoothSelectionFilter F x h) (nhds (0 : ℝ)) :=
    ht.mono_right nhdsWithin_le_nhds
  have hbase :
      Tendsto (fun p : JacobianMap × Point × ℝ ↦ x + p.2.2 • p.2.1)
        (semismoothSelectionFilter F x h) (nhds x) := by
    -- The base points `x + t • h'` converge back to `x` because `h' → h` and `t ↓ 0`.
    have hsmul :
        Tendsto (fun p : JacobianMap × Point × ℝ ↦ p.2.2 • p.2.1)
          (semismoothSelectionFilter F x h) (nhds (0 : Point)) := by
      have hsmul_pair :
          Tendsto (fun p : JacobianMap × Point × ℝ ↦ (p.2.2, p.2.1))
            (semismoothSelectionFilter F x h) (nhds ((0 : ℝ), h)) := by
        simpa [nhds_prod_eq] using (Filter.Tendsto.prodMk ht0 hh')
      have hsmul' :
          Tendsto (((fun q : ℝ × Point ↦ q.1 • q.2) : ℝ × Point → Point) ∘
              fun p : JacobianMap × Point × ℝ ↦ (p.2.2, p.2.1))
            (semismoothSelectionFilter F x h)
            (nhds ((((0 : ℝ), h).1) • (((0 : ℝ), h).2) : Point)) :=
        ((continuous_fst.smul continuous_snd).continuousAt.tendsto.comp hsmul_pair)
      have hsmul'' :
          Tendsto (fun p : JacobianMap × Point × ℝ ↦ p.2.2 • p.2.1)
            (semismoothSelectionFilter F x h) (nhds (0 : Point)) := by
        convert hsmul' using 1
        · funext p
          rfl
        · simp
      exact hsmul''
    simpa using Tendsto.const_add x hsmul
  have hbase_event :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        x + p.2.2 • p.2.1 ∈ s :=
    hbase (hs_open.mem_nhds hx_mem)
  have howner_event :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        p.1 ∈ generalizedJacobian F (x + p.2.2 • p.2.1) := by
    -- Membership in the generalized Jacobian is built into the selection filter's principal part.
    exact (show
      {p : JacobianMap × Point × ℝ | p.1 ∈ generalizedJacobian F (x + p.2.2 • p.2.1)} ∈
        semismoothSelectionFilter F x h from
      (by
        simpa [semismoothSelectionFilter] using
          (inf_le_left :
            semismoothSelectionFilter F x h ≤
              principal {p : JacobianMap × Point × ℝ |
                p.1 ∈ generalizedJacobian F (x + p.2.2 • p.2.1)})
            (by simp)))
  have hoperator_event :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        p.1 ∈ Metric.closedBall A (δ : ℝ) := by
    filter_upwards [hbase_event, howner_event] with p hp_base hp_owner
    exact
      generalizedJacobian_subset_closedBall_of_errorLipschitzOn
        hs_open hp_base hLip hp_owner
  have hdir_bound :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        ‖p.2.1‖ ≤ ‖h‖ + 1 := by
    -- The direction component stays in a fixed ball around `h`, so it is uniformly bounded.
    filter_upwards [hh' (Metric.ball_mem_nhds h zero_lt_one)] with p hp
    have hp' : ‖p.2.1 - h‖ < 1 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hp
    calc
      ‖p.2.1‖ = ‖(p.2.1 - h) + h‖ := by abel_nf
      _ ≤ ‖p.2.1 - h‖ + ‖h‖ := norm_add_le _ _
      _ ≤ 1 + ‖h‖ := by linarith
      _ = ‖h‖ + 1 := by ring
  have hAeval :
      Tendsto (fun p : JacobianMap × Point × ℝ ↦ A p.2.1)
        (semismoothSelectionFilter F x h) (nhds (A h)) := by
    -- The linear term depends only on the direction component `h'`.
    exact A.continuous.continuousAt.tendsto.comp hh'
  have hfirst :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        ‖(p.1 - A) p.2.1‖ < ε / 2 := by
    have hR : 0 < ‖h‖ + 1 := by positivity
    have hδ_mul :
        (δ : ℝ) * (‖h‖ + 1) = ε / 4 := by
      change (ε / (4 * (‖h‖ + 1))) * (‖h‖ + 1) = ε / 4
      field_simp [hR.ne']
    have hquarter : ε / 4 < ε / 2 := by linarith
    filter_upwards [hoperator_event, hdir_bound] with p hp_operator hp_dir
    have hp_op : ‖p.1 - A‖ ≤ (δ : ℝ) := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hp_operator
    have hbound :
        ‖(p.1 - A) p.2.1‖ ≤ (δ : ℝ) * (‖h‖ + 1) := by
      calc
        ‖(p.1 - A) p.2.1‖ ≤ ‖p.1 - A‖ * ‖p.2.1‖ := (p.1 - A).le_opNorm _
        _ ≤ (δ : ℝ) * (‖h‖ + 1) := by gcongr
    calc
      ‖(p.1 - A) p.2.1‖ ≤ (δ : ℝ) * (‖h‖ + 1) := hbound
      _ = ε / 4 := hδ_mul
      _ < ε / 2 := hquarter
  have hsecond :
      ∀ᶠ p : JacobianMap × Point × ℝ in semismoothSelectionFilter F x h,
        dist (A p.2.1) (A h) < ε / 2 :=
    (Metric.tendsto_nhds.1 hAeval) (ε / 2) (by positivity)
  -- Combine the small operator error with continuity of the linear term.
  filter_upwards [hfirst, hsecond] with p hp_first hp_second
  have hrewrite :
      semismoothLinearization p = (p.1 - A) p.2.1 + A p.2.1 := by
    simp [semismoothLinearization]
  calc
    dist (semismoothLinearization p) (A h)
        = dist (((p.1 - A) p.2.1) + A p.2.1) (A h) := by rw [hrewrite]
    _ ≤ ‖(p.1 - A) p.2.1‖ + dist (A p.2.1) (A h) := by
      calc
        dist (((p.1 - A) p.2.1) + A p.2.1) (A h)
            ≤ dist (((p.1 - A) p.2.1) + A p.2.1) (A p.2.1) +
                dist (A p.2.1) (A h) := dist_triangle _ _ _
        _ = ‖(p.1 - A) p.2.1‖ + dist (A p.2.1) (A h) := by
          simp [dist_eq_norm]
    _ < ε / 2 + ε / 2 := add_lt_add hp_first hp_second
    _ = ε := by ring

/-- Chapter14 Definition 14.8-extra-3: if `F` has a strong Fréchet derivative at `x`, then
`F` is semismooth at `x`. -/
theorem HasStrictFDerivAt.semismoothAt
    {F : Point → Point} {A : JacobianMap} {x : Point}
    (h_strict : HasStrictFDerivAt F A x) :
    SemismoothAt F x := by
  -- Unfold semismoothness into local Lipschitz regularity and per-direction linearization limits.
  rw [semismoothAt_iff]
  refine ⟨locallyLipschitzAt_of_hasStrictFDerivAt h_strict, ?_⟩
  intro h
  -- The strict derivative `A` supplies the common linearization limit in every direction `h`.
  exact ⟨A h, hasSemismoothLinearizationLimit_of_hasStrictFDerivAt (h := h) h_strict⟩

end
