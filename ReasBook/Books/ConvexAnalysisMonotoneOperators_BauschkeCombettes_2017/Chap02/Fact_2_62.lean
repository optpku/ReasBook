/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap02.Definition_2_54

-- Declarations for this item will be appended below by the statement pipeline.

universe u v

open scoped Topology

variable {H : Type u} {K : Type v}
variable [NormedAddCommGroup H] [NormedSpace ℝ H]
variable [NormedAddCommGroup K] [NormedSpace ℝ K]

/-- Helper for Fact 2.62: a neighborhood of `x` contains every sufficiently short segment
`x + t • h` with `t ∈ [0, 1]`. -/
private lemma short_segment_subset_field_domain
    {U : Set H} {x : H} (hU : U ∈ 𝓝 x) :
    ∃ r > 0, ∀ ⦃h : H⦄ ⦃t : ℝ⦄, ‖h‖ < r → t ∈ Set.Icc (0 : ℝ) 1 → x + t • h ∈ U := by
  rcases Metric.mem_nhds_iff.1 hU with ⟨r, hrpos, hr⟩
  refine ⟨r, hrpos, ?_⟩
  intro h t hh ht
  apply hr
  have ht_nonneg : 0 ≤ t := ht.1
  have ht_le_one : t ≤ 1 := ht.2
  have hnorm : ‖t • h‖ < r := by
    calc
      ‖t • h‖ = ‖t‖ * ‖h‖ := norm_smul t h
      _ = t * ‖h‖ := by rw [Real.norm_of_nonneg ht_nonneg]
      _ ≤ 1 * ‖h‖ := by gcongr
      _ = ‖h‖ := by ring
      _ < r := hh
  simpa [Metric.mem_ball, dist_eq_norm, sub_eq_add_neg, add_assoc] using hnorm

/-- Helper for Fact 2.62: the line derivative hypothesis gives the derivative of the segment curve
`s ↦ T (x + s • h)` at an arbitrary parameter `t`. -/
private lemma segment_curve_hasDerivAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v)
    (ht : x + t • h ∈ U) :
    HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t := by
  -- Recenter the line-derivative statement at `x + t • h` and convert the time shift back to `t`.
  let path : ℝ → K := fun s ↦ T ((x + t • h) + s • h)
  have hLine : HasDerivAt path (DT (x + t • h) h) 0 := by
    simpa [HasLineDerivAt, path] using hGateaux (x + t • h) ht h
  have hLineShift : HasDerivAt path (DT (x + t • h) h) (-t + t) := by
    simpa using hLine
  simpa [path, add_assoc, add_left_comm, add_comm, add_smul, smul_add, mul_comm, mul_left_comm,
    mul_assoc, one_smul] using HasDerivAt.comp_const_add (-t) t hLineShift

/-- Helper for Fact 2.62: the segment remainder has derivative
`((DT (x + t • h) - DT x) h)` within `[0, 1]`. -/
private lemma segment_remainder_hasDerivWithinAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x h : H} {t : ℝ}
    (hGateaux : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v)
    (_ht : t ∈ Set.Icc (0 : ℝ) 1)
    (hxt : x + t • h ∈ U) :
    HasDerivWithinAt
      (fun s : ℝ ↦ T (x + s • h) - T x - s • DT x h)
      ((DT (x + t • h) - DT x) h) (Set.Icc (0 : ℝ) 1) t := by
  -- Differentiate the three terms separately, then simplify the resulting linear expression.
  have hcurve :
      HasDerivAt (fun s : ℝ ↦ T (x + s • h)) (DT (x + t • h) h) t :=
    segment_curve_hasDerivAt hGateaux hxt
  have hlinear : HasDerivAt (fun s : ℝ ↦ s • DT x h) (DT x h) t := by
    simpa using (hasDerivAt_id' t).smul_const (DT x h)
  simpa [sub_eq_add_neg, ContinuousLinearMap.sub_apply] using
    ((hcurve.sub_const (T x)).sub hlinear).hasDerivWithinAt

/-- Helper for Fact 2.62: continuity of the operator field at `x` gives a uniform bound on the
remainder derivative along every short segment issuing from `x`. -/
private lemma uniform_operator_bound_on_short_segments
    {DT : H → H →L[ℝ] K} {U : Set H} {x : H}
    (hU : U ∈ 𝓝 x) (hcont : ContinuousWithinAt DT U x) :
    ∀ ε > 0, ∃ δ > 0, ∀ ⦃h : H⦄ ⦃t : ℝ⦄,
      ‖h‖ < δ → t ∈ Set.Icc (0 : ℝ) 1 →
      ‖((DT (x + t • h) - DT x) h)‖ ≤ ε * ‖h‖ := by
  intro ε εpos
  rcases short_segment_subset_field_domain hU with ⟨r, hrpos, hr⟩
  have hcontAt : ContinuousAt DT x := hcont.continuousAt hU
  rcases Metric.continuousAt_iff.1 hcontAt ε εpos with ⟨η, hηpos, hη⟩
  refine ⟨min r η, lt_min hrpos hηpos, ?_⟩
  intro h t hh ht
  have hh_r : ‖h‖ < r := lt_of_lt_of_le hh (min_le_left _ _)
  have hdist : dist (x + t • h) x < η := by
    have hdist_le : dist (x + t • h) x ≤ ‖h‖ := by
      have ht_nonneg : 0 ≤ t := ht.1
      have ht_le_one : t ≤ 1 := ht.2
      calc
        dist (x + t • h) x = ‖t • h‖ := by
          simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
        _ = ‖t‖ * ‖h‖ := norm_smul t h
        _ = t * ‖h‖ := by rw [Real.norm_of_nonneg ht_nonneg]
        _ ≤ 1 * ‖h‖ := by gcongr
        _ = ‖h‖ := by ring
    exact lt_of_le_of_lt hdist_le (lt_of_lt_of_le hh (min_le_right _ _))
  have hnorm_op : ‖DT (x + t • h) - DT x‖ < ε := by
    simpa [dist_eq_norm] using hη hdist
  calc
    ‖((DT (x + t • h) - DT x) h)‖ ≤ ‖DT (x + t • h) - DT x‖ * ‖h‖ :=
      ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε * ‖h‖ := by gcongr

/-- Fact 2.62: if a derivative field `DT` gives the Gâteaux derivative of `T` at every point of a
neighborhood `U` of `x`, and `DT` is continuous at `x` along `U` for the operator norm, then `T`
has Fréchet derivative `DT x` at `x`. -/
-- Proof sketch: restrict `T` to short line segments `t ↦ x + t • v`, identify the derivative of
-- this curve with `DT (x + t • v) v`, and integrate along `[0, 1]`; continuity of `DT` at `x`
-- then makes the remainder term `o (‖v‖)`.
theorem hasFDerivAt_of_gateauxDerivative_continuousWithinAt
    {T : H → K} {DT : H → H →L[ℝ] K} {U : Set H} {x : H}
    (hU : U ∈ 𝓝 x)
    (hGateaux : HasGateauxDerivativeOn T DT U)
    (hcont : ContinuousWithinAt DT U x) :
    HasFDerivAt T (DT x) x := by
  -- We prove the small-o remainder estimate by controlling `T` along short line segments.
  have hLine : ∀ y ∈ U, ∀ v : H, HasLineDerivAt ℝ T (DT y v) y v := by
    intro y hy v
    exact HasGateauxDerivativeWithinAt.hasLineDerivAt (hGateaux y hy) v
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε εpos
  rcases short_segment_subset_field_domain hU with ⟨r, hrpos, hr⟩
  rcases uniform_operator_bound_on_short_segments hU hcont ε εpos with ⟨δ, hδpos, hδ⟩
  refine Metric.eventually_nhds_iff.2 ⟨min r δ, lt_min hrpos hδpos, ?_⟩
  intro h hh
  have hhnorm : ‖h‖ < min r δ := by
    simpa [dist_eq_norm] using hh
  have hh_r : ‖h‖ < r := lt_of_lt_of_le hhnorm (min_le_left _ _)
  have hh_δ : ‖h‖ < δ := lt_of_lt_of_le hhnorm (min_le_right _ _)
  have hseg :
      ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) 1 → x + t • h ∈ U := by
    intro t ht
    exact hr hh_r ht
  have hderiv :
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt
          (fun s : ℝ ↦ T (x + s • h) - T x - s • DT x h)
          ((DT (x + t • h) - DT x) h) (Set.Icc (0 : ℝ) 1) t := by
    intro t ht
    exact segment_remainder_hasDerivWithinAt hLine ht (hseg ht)
  have hbound :
      ∀ t ∈ Set.Ico (0 : ℝ) 1,
        ‖((DT (x + t • h) - DT x) h)‖ ≤ ε * ‖h‖ := by
    intro t ht
    exact hδ hh_δ (Set.Ico_subset_Icc_self ht)
  -- The one-dimensional mean-value estimate turns the derivative bound
  -- into the desired remainder bound.
  have hmv :
      ‖(T (x + (1 : ℝ) • h) - T x - (1 : ℝ) • DT x h) -
          (T (x + (0 : ℝ) • h) - T x - (0 : ℝ) • DT x h)‖ ≤ ε * ‖h‖ := by
    simpa using norm_image_sub_le_of_norm_deriv_le_segment_01' hderiv hbound
  simpa using hmv
