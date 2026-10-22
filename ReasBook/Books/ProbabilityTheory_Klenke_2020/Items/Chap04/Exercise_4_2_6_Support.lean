/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open MeasureTheory
open scoped BigOperators ENNReal

/-- A real-valued step function on `ℝ` is constant on the finitely many intervals cut out by a
strictly increasing finite family of breakpoints, namely on `(-∞, t₀]`, on each
`(tᵢ, tᵢ₊₁]`, and on `(tₙ, ∞)`. -/
def IsStepFunction (h : ℝ → ℝ) : Prop :=
  ∃ n : ℕ, ∃ t : Fin (n + 1) → ℝ, StrictMono t ∧
    ∃ a b : ℝ, ∃ α : Fin n → ℝ,
      h = fun x ↦
        (Set.Iic (t 0)).indicator (fun _ ↦ a) x +
          ∑ k, (Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator (fun _ ↦ α k) x +
            (Set.Ioi (t (Fin.last n))).indicator (fun _ ↦ b) x

-- Proof sketch: unfold the representation of a step function, note that `Set.Iic a`,
-- `Set.Ioc a b`, and `Set.Ioi a` are measurable in `ℝ`, each indicator summand is measurable, and
-- finite sums preserve measurability.
/-- Every real-valued step function is measurable. -/
theorem IsStepFunction.measurable {h : ℝ → ℝ} (hh : IsStepFunction h) :
    Measurable h := by
  rcases hh with ⟨n, t, ht, a, b, α, rfl⟩
  -- Each indicator summand is measurable because the defining interval is measurable.
  have hleft : Measurable ((Set.Iic (t 0)).indicator (fun _ : ℝ ↦ a)) :=
    Measurable.indicator measurable_const measurableSet_Iic
  have hmiddle :
      ∀ k : Fin n,
        Measurable
          ((Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator (fun _ : ℝ ↦ α k)) := by
    intro k
    exact Measurable.indicator measurable_const measurableSet_Ioc
  have hright : Measurable ((Set.Ioi (t (Fin.last n))).indicator (fun _ : ℝ ↦ b)) :=
    Measurable.indicator measurable_const measurableSet_Ioi
  -- Finite sums preserve measurability, so the whole step function is measurable.
  simpa using (hleft.add (Finset.measurable_sum Finset.univ fun k _ ↦ hmiddle k)).add hright

/-- Helper for Exercise 4.2.6: the right-endpoint grid used to build a sampled
step approximation. -/
def uniformGridBreakpoint (R ρ : ℝ) {N : ℕ} (k : Fin (N + 1)) : ℝ :=
  -R + (k : ℕ) • ρ

/-- Helper for Exercise 4.2.6: the sampled step function attached to a uniform grid. -/
noncomputable def sampledStepApprox (g : ℝ → ℝ) (R ρ : ℝ) (N : ℕ) : ℝ → ℝ :=
  fun x ↦
    (Set.Iic (uniformGridBreakpoint R ρ (0 : Fin (N + 1)))).indicator (fun _ ↦ 0) x +
      (∑ k : Fin N,
        (Set.Ioc (uniformGridBreakpoint R ρ (Fin.castSucc k))
          (uniformGridBreakpoint R ρ k.succ)).indicator
          (fun _ ↦ g (uniformGridBreakpoint R ρ k.succ)) x) +
      (Set.Ioi (uniformGridBreakpoint R ρ (Fin.last N))).indicator (fun _ ↦ 0) x

/-- Helper for Exercise 4.2.6: positive mesh gives a strictly increasing breakpoint family. -/
lemma uniformGridBreakpoint_strictMono {R ρ : ℝ} (hρ : 0 < ρ) {N : ℕ} :
    StrictMono (uniformGridBreakpoint R ρ : Fin (N + 1) → ℝ) := by
  intro i j hij
  have hij' : (i : ℝ) < (j : ℝ) := by exact_mod_cast hij
  simpa [uniformGridBreakpoint, nsmul_eq_mul] using add_lt_add_left
    (mul_lt_mul_of_pos_right hij' hρ) (-R)

/-- Helper for Exercise 4.2.6: nonnegative mesh makes the breakpoint family monotone. -/
lemma uniformGridBreakpoint_mono {R ρ : ℝ} (hρ : 0 ≤ ρ) {N : ℕ} :
    Monotone (uniformGridBreakpoint R ρ : Fin (N + 1) → ℝ) := by
  intro i j hij
  have hij' : (i : ℝ) ≤ (j : ℝ) := by exact_mod_cast hij
  simpa [uniformGridBreakpoint, nsmul_eq_mul] using add_le_add_left
    (mul_le_mul_of_nonneg_right hij' hρ) (-R)

/-- Helper for Exercise 4.2.6: every sampled uniform-grid approximation is a step function. -/
lemma isStepFunction_sampledStepApprox {g : ℝ → ℝ} {R ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) :
    IsStepFunction (sampledStepApprox g R ρ N) := by
  -- The sampled approximation is already written in the required indicator-sum normal form.
  refine ⟨N, uniformGridBreakpoint R ρ, uniformGridBreakpoint_strictMono hρ, 0, 0,
    fun k ↦ g (uniformGridBreakpoint R ρ k.succ), rfl⟩

/-- Helper for Exercise 4.2.6: the sampled step approximation vanishes on the left of the grid. -/
lemma sampledStepApprox_eq_zero_of_le_left {g : ℝ → ℝ} {R ρ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    {x : ℝ} (hx : x ≤ -R) :
    sampledStepApprox g R ρ N x = 0 := by
  let t : Fin (N + 1) → ℝ := uniformGridBreakpoint R ρ
  have hmono : Monotone t := uniformGridBreakpoint_mono hρ.le
  have hsum :
      ∑ k : Fin N, (Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator
        (fun _ ↦ g (t k.succ)) x = 0 := by
    -- Every middle interval starts at or to the right of `-R`, so no cell contains `x`.
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hk : -R ≤ t (Fin.castSucc k) := by
      simpa [t, uniformGridBreakpoint] using
        hmono (show (0 : Fin (N + 1)) ≤ Fin.castSucc k by exact Fin.zero_le _)
    have hxk : x ∉ Set.Ioc (t (Fin.castSucc k)) (t k.succ) := by
      simp [Set.mem_Ioc, not_lt_of_ge (le_trans hx hk)]
    simp [Set.indicator_of_notMem hxk]
  have htail : (Set.Ioi (t (Fin.last N))).indicator (fun _ ↦ 0) x = 0 := by
    simp
  -- The left and right tails are identically zero, and the middle cells are all inactive.
  have hsum' :
      ∑ k : Fin N,
          (Set.Ioc (uniformGridBreakpoint R ρ (Fin.castSucc k))
              (uniformGridBreakpoint R ρ k.succ)).indicator
            (fun _ ↦ g (uniformGridBreakpoint R ρ k.succ)) x = 0 := by
    simpa [t] using hsum
  calc
    sampledStepApprox g R ρ N x = (0 : ℝ) + 0 + 0 := by
      simp [sampledStepApprox, hsum']
    _ = 0 := by ring_nf

/-- Helper for Exercise 4.2.6: the sampled step approximation vanishes to the right of the grid. -/
lemma sampledStepApprox_eq_zero_of_right_lt {g : ℝ → ℝ} {R ρ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    {x : ℝ} (hx : uniformGridBreakpoint R ρ (Fin.last N) < x) :
    sampledStepApprox g R ρ N x = 0 := by
  let t : Fin (N + 1) → ℝ := uniformGridBreakpoint R ρ
  have hmono : Monotone t := uniformGridBreakpoint_mono hρ.le
  have hsum :
      ∑ k : Fin N, (Set.Ioc (t (Fin.castSucc k)) (t k.succ)).indicator
        (fun _ ↦ g (t k.succ)) x = 0 := by
    -- Every cell ends at or before the final breakpoint, so no cell contains `x`.
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hk : t k.succ ≤ t (Fin.last N) := by
      exact hmono (by exact_mod_cast Nat.succ_le_of_lt k.is_lt)
    have hxk : x ∉ Set.Ioc (t (Fin.castSucc k)) (t k.succ) := by
      simp [Set.mem_Ioc, not_le_of_gt (lt_of_le_of_lt hk hx)]
    simp [Set.indicator_of_notMem hxk]
  have hleft : (Set.Iic (t (0 : Fin (N + 1)))).indicator (fun _ ↦ 0) x = 0 := by
    simp
  -- The two tails are zero by construction, and the middle cells end before `x`.
  have hsum' :
      ∑ k : Fin N,
          (Set.Ioc (uniformGridBreakpoint R ρ (Fin.castSucc k))
              (uniformGridBreakpoint R ρ k.succ)).indicator
            (fun _ ↦ g (uniformGridBreakpoint R ρ k.succ)) x = 0 := by
    simpa [t] using hsum
  calc
    sampledStepApprox g R ρ N x = (0 : ℝ) + 0 + 0 := by
      simp [sampledStepApprox, hsum']
    _ = 0 := by ring_nf

/-- Helper for Exercise 4.2.6: on each grid cell, the sampled approximation is the right-endpoint
sample of `g`. -/
lemma sampledStepApprox_eq_rightSample_on_cell {g : ℝ → ℝ} {R ρ : ℝ} {N : ℕ} (hρ : 0 < ρ)
    {k : Fin N} {x : ℝ}
    (hx : x ∈ Set.Ioc (uniformGridBreakpoint R ρ (Fin.castSucc k))
      (uniformGridBreakpoint R ρ k.succ)) :
    sampledStepApprox g R ρ N x = g (uniformGridBreakpoint R ρ k.succ) := by
  let t : Fin (N + 1) → ℝ := uniformGridBreakpoint R ρ
  have hmono : Monotone t := uniformGridBreakpoint_mono hρ.le
  have hsum :
      ∑ j : Fin N, (Set.Ioc (t (Fin.castSucc j)) (t j.succ)).indicator
        (fun _ ↦ g (t j.succ)) x = g (t k.succ) := by
    -- Only the unique cell containing `x` contributes to the finite sum.
    rw [Finset.sum_eq_single k]
    · simp [hx, t]
    · intro j _ hj
      have hxj : x ∉ Set.Ioc (t (Fin.castSucc j)) (t j.succ) := by
        rcases lt_or_gt_of_ne hj with hjk | hkj
        · have hu : t j.succ ≤ t (Fin.castSucc k) := by
            exact hmono (by
              exact_mod_cast Nat.succ_le_of_lt hjk)
          simp [Set.mem_Ioc, not_le_of_gt (lt_of_le_of_lt hu hx.1)]
        · have hl : t k.succ ≤ t (Fin.castSucc j) := by
            exact hmono (by
              exact_mod_cast Nat.succ_le_of_lt hkj)
          simp [Set.mem_Ioc, not_lt_of_ge (le_trans hx.2 hl)]
      simp [Set.indicator_of_notMem hxj]
    · simp
  -- The tails vanish at an interior grid point, so only the active cell remains.
  rw [sampledStepApprox, hsum]
  simp [t]

/-- Helper for Exercise 4.2.6: the support of the sampled grid approximation stays inside the
closed grid interval. -/
lemma sampledStepApprox_support_subset_interval {g : ℝ → ℝ} {R ρ : ℝ} {N : ℕ} (hρ : 0 < ρ) :
    Function.support (sampledStepApprox g R ρ N) ⊆
      Set.Icc (-R) (uniformGridBreakpoint R ρ (Fin.last N)) := by
  refine Function.support_subset_iff'.2 ?_
  intro x hx
  by_cases hleft : x ≤ -R
  · exact sampledStepApprox_eq_zero_of_le_left hρ hleft
  have hright : uniformGridBreakpoint R ρ (Fin.last N) < x := by
    by_contra hright
    apply hx
    exact ⟨le_of_lt (lt_of_not_ge hleft), le_of_not_gt hright⟩
  exact sampledStepApprox_eq_zero_of_right_lt hρ hright

/-- Helper for Exercise 4.2.6: a sufficiently fine grid gives a uniform pointwise error bound for
the sampled step approximation. -/
lemma dist_sampledStepApprox_le_of_mesh {g : ℝ → ℝ} {R ρ c : ℝ} {N : ℕ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    (hsub : tsupport g ⊆ Set.Ioo (-R) (uniformGridBreakpoint R ρ (Fin.last N)))
    (hmod : ∀ ⦃x y⦄,
      x ∈ Set.Icc (-R) (uniformGridBreakpoint R ρ (Fin.last N)) →
      y ∈ Set.Icc (-R) (uniformGridBreakpoint R ρ (Fin.last N)) →
      dist x y ≤ ρ → dist (g x) (g y) ≤ c) :
    ∀ x, dist (g x) (sampledStepApprox g R ρ N x) ≤ c := by
  intro x
  by_cases hleft : x ≤ -R
  · have hxnot : x ∉ tsupport g := by
      intro hxmem
      exact not_lt_of_ge hleft (hsub hxmem).1
    -- On the left tail both functions vanish, so the error is zero.
    simp [sampledStepApprox_eq_zero_of_le_left hρ hleft,
      image_eq_zero_of_notMem_tsupport hxnot, hc]
  by_cases hright : uniformGridBreakpoint R ρ (Fin.last N) < x
  · have hxnot : x ∉ tsupport g := by
      intro hxmem
      linarith [(hsub hxmem).2]
    -- On the right tail both functions vanish, so the error is zero.
    simp [sampledStepApprox_eq_zero_of_right_lt hρ hright,
      image_eq_zero_of_notMem_tsupport hxnot, hc]
  have hxI :
      x ∈ Set.Ioc (-R) (uniformGridBreakpoint R ρ (Fin.last N)) := by
    exact ⟨lt_of_not_ge hleft, le_of_not_gt hright⟩
  have hxcover := Ioc_subset_biUnion_Ioc N (fun n : ℕ ↦ -R + n * ρ) (by
    simpa [uniformGridBreakpoint, nsmul_eq_mul] using hxI)
  rcases Set.mem_iUnion.1 hxcover with ⟨i, hxi⟩
  rcases Set.mem_iUnion.1 hxi with ⟨hi, hxcell_nat⟩
  rcases Finset.mem_range.1 hi with hiN
  let k : Fin N := ⟨i, hiN⟩
  have hxcell :
      x ∈ Set.Ioc (uniformGridBreakpoint R ρ (Fin.castSucc k))
        (uniformGridBreakpoint R ρ k.succ) := by
    simpa [k, uniformGridBreakpoint, nsmul_eq_mul]
      using hxcell_nat
  have hk_left : -R ≤ uniformGridBreakpoint R ρ k.succ := by
    have hmono : Monotone (uniformGridBreakpoint R ρ : Fin (N + 1) → ℝ) :=
      uniformGridBreakpoint_mono hρ.le
    calc
      -R = uniformGridBreakpoint R ρ (0 : Fin (N + 1)) := by
        simp [uniformGridBreakpoint]
      _ ≤ uniformGridBreakpoint R ρ k.succ := by
        exact hmono (Fin.zero_le _)
  have hk_right :
      uniformGridBreakpoint R ρ k.succ ≤ uniformGridBreakpoint R ρ (Fin.last N) := by
    have hmono : Monotone (uniformGridBreakpoint R ρ : Fin (N + 1) → ℝ) :=
      uniformGridBreakpoint_mono hρ.le
    exact hmono (Fin.le_iff_val_le_val.mpr (Nat.succ_le_of_lt k.is_lt))
  have hk_mem :
      uniformGridBreakpoint R ρ k.succ ∈
        Set.Icc (-R) (uniformGridBreakpoint R ρ (Fin.last N)) := by
    exact ⟨hk_left, hk_right⟩
  have hdist_mesh : dist x (uniformGridBreakpoint R ρ k.succ) ≤ ρ := by
    rw [dist_comm, Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hxcell.2)]
    have hstep :
        uniformGridBreakpoint R ρ k.succ =
          uniformGridBreakpoint R ρ (Fin.castSucc k) + ρ := by
      simp [uniformGridBreakpoint, nsmul_eq_mul]
      ring_nf
    linarith [hxcell.1, hxcell.2]
  -- Inside a cell, compare `g x` with the right-endpoint sample via the uniform modulus.
  simpa [sampledStepApprox_eq_rightSample_on_cell hρ hxcell] using hmod
    (by exact ⟨le_of_lt (lt_of_not_ge hleft), le_of_not_gt hright⟩) hk_mem hdist_mesh

namespace IsStepFunction

/-- A real-valued step function on `ℝ` has finite range. -/
theorem finite_range {h : ℝ → ℝ} (hh : IsStepFunction h) :
    (Set.range h).Finite := by
  rcases hh with ⟨n, t, ht, a, b, α, rfl⟩
  let choices : Bool × (Fin n → Bool) × Bool → ℝ := fun u ↦
    (if u.1 then a else 0) + (∑ k : Fin n, if u.2.1 k then α k else 0) + if u.2.2 then b else 0
  -- A step function factors through the finite Boolean data recording which indicators fire.
  refine (Set.finite_range choices).subset ?_
  rintro y ⟨x, rfl⟩
  refine ⟨(x ∈ Set.Iic (t 0), fun k : Fin n ↦ x ∈ Set.Ioc (t (Fin.castSucc k)) (t k.succ),
      x ∈ Set.Ioi (t (Fin.last n))), ?_⟩
  simp [choices, Set.indicator_apply]

end IsStepFunction

/-- Helper for Exercise 4.2.6: a compact topological support fits inside a symmetric open
interval. -/
lemma exists_pos_radius_tsupport_subset_Ioo {g : ℝ → ℝ} (hg : HasCompactSupport g) :
    ∃ R > 0, tsupport g ⊆ Set.Ioo (-R) R := by
  -- Compact support is bounded, so it sits inside some open ball around the origin.
  obtain ⟨R, hR, hsub⟩ := hg.isCompact.isBounded.subset_ball_lt (0 : ℝ) 0
  refine ⟨R, hR, ?_⟩
  simpa [Real.ball_eq_Ioo] using hsub

/-- Helper for Exercise 4.2.6: the mesh `2 * R / (n + 1)` makes the last breakpoint equal to
`R`. -/
lemma uniformGridBreakpoint_last_eq_rightEndpoint {R : ℝ} {n : ℕ} :
    uniformGridBreakpoint R (2 * R / (n + 1 : ℝ)) (Fin.last (n + 1)) = R := by
  have hN : (n + 1 : ℝ) ≠ 0 := by positivity
  -- Evaluate the last breakpoint and simplify the resulting affine expression.
  rw [uniformGridBreakpoint, Fin.val_last, nsmul_eq_mul]
  have hmul : (↑(n + 1) : ℝ) * (2 * R / (↑n + 1)) = 2 * R := by
    have hcast : (↑(n + 1) : ℝ) = ↑n + 1 := by
      norm_num [Nat.cast_add]
    rw [hcast]
    field_simp [hN]
  calc
    -R + (↑(n + 1) : ℝ) * (2 * R / (↑n + 1)) = -R + 2 * R := by rw [hmul]
    _ = R := by ring_nf

/-- Helper for Exercise 4.2.6: a uniform pointwise bound on the fixed interval `[-R, R]` gives the
final `eLpNorm` control for the sampled step approximation. -/
lemma eLpNorm_sub_sampledStepApprox_lt_of_uniformBound
    {p R c ε : ℝ} (hR : 0 < R) (hc : 0 ≤ c) {g : ℝ → ℝ} {n : ℕ}
    (hsub : tsupport g ⊆ Set.Ioo (-R) R)
    (hmod : ∀ ⦃x y⦄, x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
      dist x y ≤ 2 * R / (n + 1 : ℝ) → dist (g x) (g y) ≤ c)
    (hcε : ENNReal.ofReal c * volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) <
      ENNReal.ofReal ε) :
    eLpNorm (g - sampledStepApprox g R (2 * R / (n + 1 : ℝ)) (n + 1))
      (ENNReal.ofReal p) volume < ENNReal.ofReal ε := by
  let ρ : ℝ := 2 * R / (n + 1 : ℝ)
  have hρ : 0 < ρ := by
    -- The symmetric interval has positive width, so the chosen mesh is positive.
    dsimp [ρ]
    positivity
  have hdist : ∀ x, dist (g x) (sampledStepApprox g R ρ (n + 1) x) ≤ c := by
    -- The sampled-grid pointwise estimate now matches the fixed interval after endpoint
    -- normalization.
    apply dist_sampledStepApprox_le_of_mesh (g := g) (R := R) (ρ := ρ) (c := c) (N := n + 1) hρ hc
    · simpa [ρ, uniformGridBreakpoint_last_eq_rightEndpoint] using hsub
    · simpa [ρ, uniformGridBreakpoint_last_eq_rightEndpoint] using hmod
  have hsupp_g : Function.support g ⊆ Set.Icc (-R) R := by
    -- Points where `g` is nonzero lie in `tsupport g`, hence inside the fixed interval.
    intro x hx
    exact ⟨le_of_lt (hsub (subset_tsupport g hx)).1, le_of_lt (hsub (subset_tsupport g hx)).2⟩
  have hsupp_step :
      Function.support (sampledStepApprox g R ρ (n + 1)) ⊆ Set.Icc (-R) R := by
    -- The sampled step function has the same fixed compact interval as support container.
    simpa [ρ, uniformGridBreakpoint_last_eq_rightEndpoint] using
      sampledStepApprox_support_subset_interval (g := g) (R := R) (ρ := ρ) (N := n + 1) hρ
  have hnorm_le :
      eLpNorm (g - sampledStepApprox g R ρ (n + 1)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal c * volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) := by
    -- Once both supports are inside `[-R, R]`, the standard `eLpNorm` estimate applies directly.
    exact MeasureTheory.eLpNorm_sub_le_of_dist_bdd (μ := volume) ENNReal.ofReal_ne_top
      measurableSet_Icc hc hdist hsupp_g hsupp_step
  simpa [ρ] using lt_of_le_of_lt hnorm_le hcε

/-- Helper for Exercise 4.2.6: choose a positive pointwise error budget whose interval-factor
bound is already below `ε`. -/
lemma exists_posPointwiseBudget_lt_intervalFactor
    {p R ε : ℝ} (hp : 1 ≤ p) (hε : 0 < ε) :
    ∃ c > 0,
      ENNReal.ofReal c * volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) <
        ENNReal.ofReal ε := by
  have hp_pos : 0 < p := by
    linarith
  have hexponent_nonneg : 0 ≤ 1 / (ENNReal.ofReal p).toReal := by
    have hp_toReal_pos : 0 < (ENNReal.ofReal p).toReal := by
      simpa [ENNReal.toReal_ofReal hp_pos.le] using hp_pos
    positivity
  have hfactor_top :
      volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) ≠ ⊤ := by
    -- The interval has finite volume, so its `rpow` factor may be converted to a real number.
    exact ENNReal.rpow_ne_top_of_nonneg hexponent_nonneg measure_Icc_lt_top.ne
  set M : ℝ := (volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal)).toReal
  obtain ⟨c, hcpos, hcsmall⟩ := exists_pos_mul_lt hε M
  have hM :
      ENNReal.ofReal M = volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) := by
    -- This is the only place where the finite interval factor is rewritten through `toReal`.
    simp [M]
  refine ⟨c, hcpos, ?_⟩
  -- The chosen pointwise budget is exactly small enough for the final `eLpNorm` estimate.
  calc
    ENNReal.ofReal c * volume (Set.Icc (-R) R) ^ (1 / (ENNReal.ofReal p).toReal) =
        ENNReal.ofReal c * ENNReal.ofReal M := by rw [← hM]
    _ = ENNReal.ofReal (c * M) := by rw [ENNReal.ofReal_mul hcpos.le]
    _ = ENNReal.ofReal (M * c) := by rw [mul_comm]
    _ < ENNReal.ofReal ε := by
      exact (ENNReal.ofReal_lt_ofReal_iff hε).2 hcsmall

/-- Helper for Exercise 4.2.6: continuity on `ℝ` yields a quantitative modulus on each compact
interval `[-R, R]`. -/
lemma exists_uniformDistanceBoundOnIcc_of_continuous
    {g : ℝ → ℝ} (hg_cont : Continuous g) {R c : ℝ} (hc : 0 < c) :
    ∃ δ > 0, ∀ ⦃x y⦄,
      x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
        dist x y ≤ δ → dist (g x) (g y) ≤ c := by
  have huc : UniformContinuousOn g (Set.Icc (-R) R) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hg_cont.continuousOn
  obtain ⟨δ, hδpos, hδmod⟩ := (Metric.uniformContinuousOn_iff_le.1 huc) c hc
  refine ⟨δ, hδpos, ?_⟩
  -- The compact-interval modulus is now packaged in the exact shape used by the grid estimate.
  intro x y hx hy hxy
  exact hδmod x hx y hy hxy

/-- Helper for Exercise 4.2.6: a positive target mesh size is eventually larger than the uniform
grid spacing `2 * R / (n + 1)`. -/
lemma exists_uniformGridMesh_lt_of_pos {R δ : ℝ} (_hR : 0 < R) (hδ : 0 < δ) :
    ∃ n : ℕ, 2 * R / (n + 1 : ℝ) < δ := by
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * R / δ)
  have hn' : 2 * R / δ < (n + 1 : ℝ) := by
    exact lt_of_lt_of_le hn (by exact_mod_cast Nat.le_succ n)
  refine ⟨n, ?_⟩
  -- Rewriting the target inequality once keeps the final approximation theorem arithmetic-free.
  refine (div_lt_iff₀ (show 0 < (n + 1 : ℝ) by positivity)).2 ?_
  have hmul : 2 * R < (n + 1 : ℝ) * δ := by
    exact (div_lt_iff₀ hδ).1 hn'
  linarith

/-- Helper for Exercise 4.2.6: compactly supported continuous functions admit arbitrarily small
`eLpNorm` approximations by step functions. -/
lemma exists_stepFunction_eLpNorm_sub_lt_of_hasCompactSupport_continuous
    {p : ℝ} (hp : 1 ≤ p) {g : ℝ → ℝ}
    (hg_compact : HasCompactSupport g) (hg_cont : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℝ,
      IsStepFunction h ∧
        eLpNorm (g - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := by
  -- Route correction: freeze the support inside one symmetric interval so endpoint normalization
  -- and the `eLpNorm` estimate are both handled on the fixed set `Set.Icc (-R) R`.
  obtain ⟨R, hR, hsub⟩ := exists_pos_radius_tsupport_subset_Ioo hg_compact
  obtain ⟨c, hcpos, hcε⟩ := exists_posPointwiseBudget_lt_intervalFactor (R := R) hp hε
  obtain ⟨δ, hδpos, hδmod⟩ :=
    exists_uniformDistanceBoundOnIcc_of_continuous (R := R) hg_cont hcpos
  obtain ⟨n, hmesh_lt⟩ := exists_uniformGridMesh_lt_of_pos (R := R) hR hδpos
  have hmod_mesh :
      ∀ ⦃x y⦄, x ∈ Set.Icc (-R) R → y ∈ Set.Icc (-R) R →
        dist x y ≤ 2 * R / (n + 1 : ℝ) → dist (g x) (g y) ≤ c := by
    -- Any pair in the same grid cell is within the modulus scale, so the pointwise error is `≤ c`.
    intro x y hx hy hxy
    exact hδmod hx hy (le_trans hxy hmesh_lt.le)
  let h : ℝ → ℝ := sampledStepApprox g R (2 * R / (n + 1 : ℝ)) (n + 1)
  have hh_step : IsStepFunction h := by
    -- Positive mesh puts the sampled approximation in the required step-function normal form.
    simpa [h] using isStepFunction_sampledStepApprox (g := g) (R := R)
      (ρ := 2 * R / (n + 1 : ℝ)) (N := n + 1) (by positivity)
  have hnorm :
      eLpNorm (g - h) (ENNReal.ofReal p) volume < ENNReal.ofReal ε := by
    -- The fixed-interval closing lemma packages the sampled-grid support and norm bookkeeping.
    simpa [h] using
      eLpNorm_sub_sampledStepApprox_lt_of_uniformBound (p := p) (R := R) (c := c) (ε := ε)
        hR hcpos.le (g := g) (n := n) hsub hmod_mesh hcε
  exact ⟨h, hh_step, hnorm⟩
