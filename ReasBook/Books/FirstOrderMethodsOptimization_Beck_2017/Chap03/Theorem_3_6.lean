/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_2
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_6
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Definition_3_7
import FirstOrderMethodsOptimization_Beck_2017.Chap03.Theorem_3_2

-- Declarations for this item will be appended below by the statement pipeline.

universe u

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/- Theorem 3.6 is a `source-facing` existence statement in the chapter convex-analysis API.
Its owner notions are already provided earlier in the project by `effective_domain`,
`is_convex_function`, `subdifferential`, `subdifferential_domain`, and `intrinsicInterior ℝ`, so
this file reuses those declarations directly rather than restating local copies. The relative-
interior hypothesis already forces `effective_domain f` to be nonempty, and for a convex
extended-real-valued function any occurrence of `⊥` is either absent on the effective domain or
makes every dual vector a subgradient there. Thus the theorem needs only the owner convexity and
relative-interior hypotheses. -/
recall effective_domain
recall is_convex_function
recall subdifferential
recall subdifferential_domain
recall mem_subdifferential_domain
recall intrinsicInterior

-- Proof sketch: translate the textbook relative-interior hypothesis on `effective_domain f` into
-- the finite-dimensional supporting-hyperplane setup for the epigraph of `f`. A supporting
-- functional at `(x, f x)` has positive vertical coefficient, and normalizing it yields a linear
-- functional satisfying the subgradient inequality at `x`. If `f` takes the value `⊥` somewhere
-- on the effective domain, convexity forces the same at every relative-interior point, and then
-- the subgradient inequality is automatic for every dual vector.
/-- Helper for Theorem 3.6: if `f x = ⊥`, then the zero functional is already a subgradient at
`x`. -/
lemma zero_mem_subdifferential_of_eq_bot
    (f : E → EReal) (x : E) (hx : x ∈ effective_domain f) (hfx : f x = ⊥) :
    (0 : Module.Dual ℝ E) ∈ ∂ f(x) := by
  -- Rewrite the owner predicate so only the effective-domain inequality remains.
  rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
  refine ⟨hx, ?_⟩
  intro y hy
  -- Once `f x = ⊥`, the affine lower bound is the bottom element and is automatic.
  simp [hfx]

/-- Helper for Theorem 3.6: translating `effective_domain f` by `-x` along the direction of its
affine span turns the relative-interior hypothesis at `x` into an ordinary interior statement at
`0`. -/
lemma translatedEffectiveDomainZero_mem_interior
    (f : E → EReal) (x : E) (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) :
    (0 : (affineSpan ℝ (effective_domain f)).direction) ∈
      interior
        {v : (affineSpan ℝ (effective_domain f)).direction | x + (v : E) ∈ effective_domain f} := by
  rcases (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset).1 hx with
    ⟨hx_aff, ε, hε, hεsub⟩
  -- A metric ball around `0` in the direction space maps into the closed-ball neighborhood around
  -- `x` guaranteed by the intrinsic-interior characterization.
  refine mem_interior_iff_mem_nhds.2 <|
    Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) ?_
  intro v hv
  have hxv_aff : x + (v : E) ∈ affineSpan ℝ (effective_domain f) := by
    simpa [add_comm] using
      AffineSubspace.vadd_mem_of_mem_direction
        (s := affineSpan ℝ (effective_domain f)) v.property hx_aff
  have hxv_ball : x + (v : E) ∈ Metric.closedBall x ε := by
    change dist (x + (v : E)) x ≤ ε
    have hv0 : dist (v : E) 0 < ε := by
      change dist v 0 < ε
      exact hv
    have hv' : dist (x + (v : E)) x < ε := by
      calc
        dist (x + (v : E)) x = dist (v : E) 0 := by
          simp [dist_eq_norm, sub_eq_add_neg, add_assoc]
        _ < ε := hv0
    exact le_of_lt hv'
  exact hεsub ⟨hxv_ball, hxv_aff⟩

/-- Helper for Theorem 3.6: once `f x` avoids `⊥` at a relative-interior point of
`effective_domain f`, convexity prevents `f` from taking the value `⊥` anywhere else on the
effective domain. -/
lemma neBot_on_effectiveDomain_of_neBot_at_relativeInterior
    (f : E → EReal) (x : E) (hconv : is_convex_function f)
    (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) (hfx : f x ≠ ⊥) :
    ∀ y ∈ effective_domain f, f y ≠ ⊥ := by
  intro y hy hfy
  let P : Submodule ℝ E := (affineSpan ℝ (effective_domain f)).direction
  have hx_aff : x ∈ affineSpan ℝ (effective_domain f) := by
    exact (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset.1 hx).1
  have hy_aff : y ∈ affineSpan ℝ (effective_domain f) := by
    exact subset_affineSpan ℝ (effective_domain f) hy
  let v : P := ⟨y - x, by
    simpa using (affineSpan ℝ (effective_domain f)).vsub_mem_direction hy_aff hx_aff⟩
  have hzero_int :
      (0 : P) ∈ interior {w : P | x + (w : E) ∈ effective_domain f} :=
    translatedEffectiveDomainZero_mem_interior f x hx
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hzero_int) with ⟨ε, hε, hball⟩
  by_cases hv : v = 0
  · -- If the translated direction vanishes, then `y = x`, contradicting `f x ≠ ⊥`.
    have hxy : y = x := by
      have hv' : (v : E) = 0 := by
        simpa [v] using congrArg (fun w : P => (w : E)) hv
      exact sub_eq_zero.mp <| by simpa [v] using hv'
    subst hxy
    exact hfx hfy
  · let t : ℝ := min 1 (ε / (‖v‖ + 1))
    have ht_pos : 0 < t := by
      dsimp [t]
      refine lt_min zero_lt_one ?_
      positivity
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hnorm_lt : ‖(-t) • v‖ < ε := by
      have hle : t ≤ ε / (‖v‖ + 1) := by
        dsimp [t]
        exact min_le_right _ _
      have hden : 0 < ‖v‖ + 1 := by positivity
      have hscaled : t * (‖v‖ + 1) ≤ ε := by
        have hmul := mul_le_mul_of_nonneg_right hle hden.le
        calc
          t * (‖v‖ + 1) ≤ (ε / (‖v‖ + 1)) * (‖v‖ + 1) := hmul
          _ = ε := by field_simp [hden.ne']
      have hlt_aux : t * ‖v‖ < t * (‖v‖ + 1) := by
        nlinarith [ht_pos]
      have htv : t * ‖v‖ < ε := lt_of_lt_of_le hlt_aux hscaled
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using htv
    have hw_mem : (-t) • v ∈ Metric.ball (0 : P) ε := by
      simpa [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm, neg_smul] using hnorm_lt
    -- Step outside `x` in the direction away from `y` while staying inside the effective domain.
    have hz_mem : x + (((-t) • v : P) : E) ∈ effective_domain f := hball hw_mem
    let z : E := x + (((-t) • v : P) : E)
    let θ : ℝ := t / (1 + t)
    have hθ : θ ∈ Set.Ioo (0 : ℝ) 1 := by
      dsimp [θ]
      constructor
      · positivity
      · have ht1 : 0 < 1 + t := by positivity
        have htt : t < 1 + t := by linarith
        exact (div_lt_one ht1).2 htt
    have hz_epi : f z ≤ ((f z).toReal : EReal) := by
      exact EReal.le_coe_toReal (ne_of_lt (by simpa [z, effective_domain] using hz_mem))
    -- Rewrite `x` as a strict convex combination of `y` and the nearby point `z`.
    have hx_combo : x = θ • y + (1 - θ) • z := by
      have hx_combo' :
          x = (t / (1 + t)) • y + (1 - t / (1 + t)) • (x + (-t) • (y - x)) := by
        have ht1 : (1 + t) ≠ 0 := by positivity
        rw [Convex.combo_eq_smul_sub_add (by ring : t / (1 + t) + (1 - t / (1 + t)) = 1)]
        have hθ' : 1 - t / (1 + t) = 1 / (1 + t) := by
          field_simp [ht1]
          ring
        rw [hθ']
        have hz_sub : (x + (-t) • (y - x)) - y = (1 + t) • (x - y) := by
          calc
            (x + (-t) • (y - x)) - y = x + t • x - (y + t • y) := by
              simp [sub_eq_add_neg]
              abel
            _ = (1 + t) • (x - y) := by
              rw [smul_sub, add_smul, add_smul]
              simp [sub_eq_add_neg, add_comm, add_assoc]
        rw [hz_sub, smul_smul]
        field_simp [ht1]
        simp
      simpa [θ, z, v] using hx_combo'
    have hepigraph : Convex ℝ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
      simpa [is_convex_function] using hconv
    have hbelow (R : ℝ) : f x ≤ (R : EReal) := by
      let ry : ℝ := (R - (1 - θ) * (f z).toReal) / θ
      have hy_epi : ((y, ry) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        simp [ry, hfy]
      have hz_epi' : ((z, (f z).toReal) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        simpa using hz_epi
      have hcombo_mem :
          θ • ((y, ry) : E × ℝ) + (1 - θ) • ((z, (f z).toReal) : E × ℝ) ∈
            {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} :=
        hepigraph hy_epi hz_epi' hθ.1.le (sub_nonneg.mpr hθ.2.le) (by ring)
      have hpair :
          ((x, R) : E × ℝ) =
            θ • ((y, ry) : E × ℝ) + (1 - θ) • ((z, (f z).toReal) : E × ℝ) := by
        ext
        · simpa [ry] using hx_combo
        · dsimp [ry]
          field_simp [hθ.1.ne']
          ring_nf
      have hxR_mem : ((x, R) : E × ℝ) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
        exact hpair ▸ hcombo_mem
      exact hxR_mem
    -- Since the epigraph contains `(x, R)` for every real `R`, the value at `x` must be `⊥`.
    have hbot : f x = ⊥ := by
      rw [EReal.eq_bot_iff_forall_lt]
      intro R
      have hltR : (R - 1 : ℝ) < R := by linarith
      exact lt_of_le_of_lt (hbelow (R - 1)) (by exact_mod_cast hltR)
    exact hfx hbot

/-- Helper for Theorem 3.6: the graph point `(0, φ 0)` of a convex real-valued function on a
domain containing `0` admits a supporting functional on its epigraph. -/
lemma supportAtGraphPoint_of_convexEpigraph
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {domP : Set P} {φ : P → ℝ} (hφ : ConvexOn ℝ domP φ) (hzero_dom : (0 : P) ∈ domP) :
    ∃ L : StrongDual ℝ (P × ℝ), L ≠ 0 ∧
      ∀ p : P × ℝ, p.1 ∈ domP → φ p.1 ≤ p.2 → L p ≤ L (0, φ 0) := by
  let S : Set (P × ℝ) := {p | p.1 ∈ domP ∧ φ p.1 ≤ p.2}
  have hS_nonempty : S.Nonempty := by
    -- The point one unit above the graph is always in the epigraph.
    refine ⟨(0, φ 0 + 1), ?_⟩
    exact ⟨hzero_dom, by linarith⟩
  have hS_convex : Convex ℝ S := by
    -- The owner convexity theorem rewrites the epigraph exactly in the required shape.
    simpa [S] using hφ.convex_epigraph
  have hgraph_not_mem : ((0 : P), φ 0) ∉ interior S := by
    intro hmem
    rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hmem) with ⟨ε, hε, hball⟩
    have hfst :
        (0 : P) ∈ Metric.ball (0 : P) ε := by
      simpa [Metric.mem_ball] using hε
    have hsnd :
        φ 0 - ε / 2 ∈ Metric.ball (φ 0) ε := by
      have hhalf : ε / 2 < ε := by linarith
      have habs : |(φ 0 - ε / 2) - φ 0| = ε / 2 := by
        have hcalc : (φ 0 - ε / 2) - φ 0 = -(ε / 2) := by ring
        rw [hcalc, abs_neg, abs_of_nonneg (by positivity)]
      have hhalf' : |ε| / 2 < ε := by
        simpa [abs_of_pos hε] using hhalf
      simpa [Metric.mem_ball, Real.dist_eq, habs] using hhalf'
    have hdown_prod :
        ((0 : P), φ 0 - ε / 2) ∈ Metric.ball (0 : P) ε ×ˢ Metric.ball (φ 0) ε := by
      exact ⟨hfst, hsnd⟩
    have hdown_ball :
        ((0 : P), φ 0 - ε / 2) ∈ Metric.ball ((0 : P), φ 0) ε := by
      simpa [ball_prod_same] using hdown_prod
    have hdown_mem : ((0 : P), φ 0 - ε / 2) ∈ S := hball hdown_ball
    have : φ 0 ≤ φ 0 - ε / 2 := hdown_mem.2
    linarith
  -- Theorem 3.2 supplies a nonzero supporting functional at the boundary point.
  rcases supporting_hyperplane_of_not_mem_interior hS_nonempty hS_convex hgraph_not_mem with
    ⟨L, hLne, hLsup⟩
  exact ⟨L, hLne, fun p hpdom hpφ ↦ hLsup p ⟨hpdom, hpφ⟩⟩

/-- Helper for Theorem 3.6: any supporting functional at the graph point of a convex epigraph has
strictly negative vertical coefficient once the domain has interior at `0`. -/
lemma verticalCoefficient_strictlyNegative_of_supportOnConvexEpigraph
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    {domP : Set P} {φ : P → ℝ} {L : StrongDual ℝ (P × ℝ)}
    (hzero_int : (0 : P) ∈ interior domP) (hLne : L ≠ 0)
    (hLsup : ∀ p : P × ℝ, p.1 ∈ domP → φ p.1 ≤ p.2 → L p ≤ L (0, φ 0)) :
    L (0, (1 : ℝ)) < 0 := by
  let a : ℝ := L (0, (1 : ℝ))
  have hzero_dom : (0 : P) ∈ domP := interior_subset hzero_int
  have ha_nonpos : a ≤ 0 := by
    -- Moving vertically upward stays in the epigraph, so the support cannot increase.
    have hstep := hLsup (0, φ 0 + 1) hzero_dom (by linarith)
    have hleft : L (0, φ 0 + 1) = L (0, φ 0) + a := by
      calc
        L (0, φ 0 + 1) = L ((0, φ 0) + (0, (1 : ℝ))) := by simp
        _ = L (0, φ 0) + L (0, (1 : ℝ)) := by rw [map_add]
        _ = L (0, φ 0) + a := by simp [a]
    have hstep' : L (0, φ 0) + a ≤ L (0, φ 0) := by
      rw [← hleft]
      exact hstep
    linarith
  by_contra ha_neg
  have ha_zero : a = 0 := le_antisymm ha_nonpos (le_of_not_gt ha_neg)
  rcases Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hzero_int) with ⟨ε, hε, hball⟩
  have hdecomp : ∀ v : P, ∀ s : ℝ, L (v, s) = L (v, 0) + s * a := by
    intro v s
    calc
      L (v, s) = L ((v, 0) + (0, s)) := by simp
      _ = L (v, 0) + L (0, s) := by rw [map_add]
      _ = L (v, 0) + s * a := by
        rw [show ((0 : P), s) = s • ((0 : P), (1 : ℝ)) by simp, map_smul]
        simp [a]
  have hhorizontal_zero : ∀ v : P, L (v, (0 : ℝ)) = 0 := by
    intro v
    let t : ℝ := min 1 (ε / (‖v‖ + 1))
    have ht_pos : 0 < t := by
      dsimp [t]
      refine lt_min zero_lt_one ?_
      positivity
    have ht_nonneg : 0 ≤ t := ht_pos.le
    have hle : t ≤ ε / (‖v‖ + 1) := by
      dsimp [t]
      exact min_le_right _ _
    have hscaled : t * (‖v‖ + 1) ≤ ε := by
      have hden : 0 < ‖v‖ + 1 := by positivity
      have hmul := mul_le_mul_of_nonneg_right hle hden.le
      calc
        t * (‖v‖ + 1) ≤ (ε / (‖v‖ + 1)) * (‖v‖ + 1) := hmul
        _ = ε := by field_simp [hden.ne']
    have hnorm_lt : ‖t • v‖ < ε := by
      have hlt_aux : t * ‖v‖ < t * (‖v‖ + 1) := by
        nlinarith [ht_pos]
      have htv : t * ‖v‖ < ε := lt_of_lt_of_le hlt_aux hscaled
      simpa [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg] using htv
    have hball_pos : t • v ∈ Metric.ball (0 : P) ε := by
      simpa [Metric.mem_ball, dist_eq_norm] using hnorm_lt
    have hball_neg : (-t) • v ∈ Metric.ball (0 : P) ε := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_neg] using hnorm_lt
    have hpos_mem : t • v ∈ domP := hball hball_pos
    have hneg_mem : (-t) • v ∈ domP := hball hball_neg
    have hpos_le := hLsup (t • v, φ (t • v)) hpos_mem le_rfl
    have hneg_le := hLsup ((-t) • v, φ ((-t) • v)) hneg_mem le_rfl
    have hpos_zero : t * L (v, (0 : ℝ)) ≤ 0 := by
      have : L (t • v, 0) + a * φ (t • v) ≤ a * φ 0 := by
        have htmp := hpos_le
        rw [hdecomp (t • v) (φ (t • v)), hdecomp 0 (φ 0)] at htmp
        have hzero_eval : L ((0 : P), (0 : ℝ)) = 0 := by
          change L (0 : P × ℝ) = 0
          exact map_zero L
        rw [hzero_eval] at htmp
        simpa [mul_comm, add_comm, add_left_comm, add_assoc, a] using htmp
      rw [ha_zero] at this
      have hraw : L (t • v, 0) ≤ 0 := by simpa using this
      have hmap : L (t • v, 0) = t * L (v, 0) := by
        calc
          L (t • v, 0) = L (t • (v, (0 : ℝ))) := by simp
          _ = t • L (v, (0 : ℝ)) := by rw [map_smul]
          _ = t * L (v, (0 : ℝ)) := by simp [smul_eq_mul]
      rw [hmap] at hraw
      exact hraw
    have hneg_zero : (-t) * L (v, (0 : ℝ)) ≤ 0 := by
      have : L ((-t) • v, 0) + a * φ ((-t) • v) ≤ a * φ 0 := by
        have htmp := hneg_le
        rw [hdecomp ((-t) • v) (φ ((-t) • v)), hdecomp 0 (φ 0)] at htmp
        have hzero_eval : L ((0 : P), (0 : ℝ)) = 0 := by
          change L (0 : P × ℝ) = 0
          exact map_zero L
        rw [hzero_eval] at htmp
        simpa [mul_comm, add_comm, add_left_comm, add_assoc, a] using htmp
      rw [ha_zero] at this
      have hraw : L ((-t) • v, 0) ≤ 0 := by simpa using this
      have hmap : L ((-t) • v, 0) = (-t) * L (v, 0) := by
        calc
          L ((-t) • v, 0) = L ((-t) • (v, (0 : ℝ))) := by simp
          _ = (-t) • L (v, (0 : ℝ)) := by rw [map_smul]
          _ = (-t) * L (v, (0 : ℝ)) := by simp [smul_eq_mul]
      rw [hmap] at hraw
      exact hraw
    have hnonneg : 0 ≤ t * L (v, (0 : ℝ)) := by
      linarith
    have hmul_zero : t * L (v, (0 : ℝ)) = 0 := le_antisymm hpos_zero hnonneg
    exact (mul_eq_zero.mp hmul_zero).resolve_left ht_pos.ne'
  have hLzero : L = 0 := by
    -- Vanishing on every horizontal slice together with zero vertical coefficient forces `L = 0`.
    apply ContinuousLinearMap.ext
    intro q
    rcases q with ⟨v, s⟩
    calc
      L (v, s) = L (v, (0 : ℝ)) + s * a := hdecomp v s
      _ = 0 := by simp [hhorizontal_zero v, ha_zero]
  exact hLne hLzero

/-- Theorem 3.6: if `f` is convex and `x` lies in the relative interior of `dom(f)`, then the
subdifferential `∂ f(x)` is nonempty. -/
theorem subdifferential_nonempty_at_relativeInterior_point
    (f : E → EReal) (x : E) (hconv : is_convex_function f)
    (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) :
    (∂ f(x)).Nonempty := by
  have hx_dom : x ∈ effective_domain f := intrinsicInterior_subset hx
  by_cases hfx : f x = ⊥
  · -- The `⊥` branch is immediate because every affine lower bound starts from bottom.
    exact ⟨0, zero_mem_subdifferential_of_eq_bot f x hx_dom hfx⟩
  · -- Route correction: the finite branch has to work in the direction space of
    -- `affineSpan ℝ (effective_domain f)` so that the translated effective domain has honest
    -- interior at `0`; the support functional is then normalized along the vertical direction and
    -- transported back with `dualLift`.
    let P : Submodule ℝ E := (affineSpan ℝ (effective_domain f)).direction
    let domP : Set P := {v : P | x + (v : E) ∈ effective_domain f}
    let φ : P → ℝ := fun v ↦ (f (x + (v : E))).toReal
    have hzero_int : (0 : P) ∈ interior domP := by
      simpa [P, domP] using translatedEffectiveDomainZero_mem_interior f x hx
    have hzero_dom : (0 : P) ∈ domP := interior_subset hzero_int
    have hne_bot_dom :
        ∀ y ∈ effective_domain f, f y ≠ ⊥ :=
      neBot_on_effectiveDomain_of_neBot_at_relativeInterior f x hconv hx hfx
    have hφ_convex : ConvexOn ℝ domP φ := by
      let translate : P →ᵃ[ℝ] E :=
        (AffineEquiv.vaddConst ℝ x).toAffineMap.comp P.subtype.toAffineMap
      -- The finite-valued convex restriction transports along the translation `v ↦ x + v`.
      simpa [P, domP, φ, translate, Function.comp, add_comm] using
        (convexOn_toReal_of_is_convex_function hconv hne_bot_dom).comp_affineMap translate
    obtain ⟨L, hLne, hLsup⟩ := supportAtGraphPoint_of_convexEpigraph hφ_convex hzero_dom
    have ha : L (0, (1 : ℝ)) < 0 :=
      verticalCoefficient_strictlyNegative_of_supportOnConvexEpigraph hzero_int hLne hLsup
    let a : ℝ := L (0, (1 : ℝ))
    let horiz : Module.Dual ℝ P := L.toLinearMap.comp (LinearMap.inl ℝ P ℝ)
    let gP : Module.Dual ℝ P := ((-a)⁻¹) • horiz
    let g : Module.Dual ℝ E := Subspace.dualLift P gP
    refine ⟨g, ?_⟩
    rw [mem_subdifferential, is_subgradient_at_iff_forall_mem_effective_domain]
    refine ⟨hx_dom, ?_⟩
    intro y hy
    have hx_aff : x ∈ affineSpan ℝ (effective_domain f) := by
      exact (mem_intrinsicInterior_iff_closedBall_inter_affineSpan_subset.1 hx).1
    have hy_aff : y ∈ affineSpan ℝ (effective_domain f) := by
      exact subset_affineSpan ℝ (effective_domain f) hy
    let v : P := ⟨y - x, by
      simpa [P] using (affineSpan ℝ (effective_domain f)).vsub_mem_direction hy_aff hx_aff⟩
    have hv_dom : v ∈ domP := by
      simpa [domP, v]
    have hsupp : L (v, φ v) ≤ L (0, φ 0) := hLsup (v, φ v) hv_dom le_rfl
    have ha_ne : a ≠ 0 := ne_of_lt ha
    have hdecomp : ∀ v' : P, ∀ s : ℝ, L (v', s) = L (v', 0) + s * a := by
      intro v' s
      calc
        L (v', s) = L ((v', 0) + (0, s)) := by simp
        _ = L (v', 0) + L (0, s) := by rw [map_add]
        _ = L (v', 0) + s * a := by
          rw [show ((0 : P), s) = s • ((0 : P), (1 : ℝ)) by simp, map_smul]
          simp [a]
    have hsupp' : L (v, 0) ≤ (-a) * (φ v - φ 0) := by
      have : L (v, 0) + a * φ v ≤ a * φ 0 := by
        have htmp := hsupp
        rw [hdecomp v (φ v), hdecomp 0 (φ 0)] at htmp
        have hzero_eval : L ((0 : P), (0 : ℝ)) = 0 := by
          change L (0 : P × ℝ) = 0
          exact map_zero L
        rw [hzero_eval] at htmp
        simpa [mul_comm, add_comm, add_left_comm, add_assoc, a] using htmp
      linarith
    have hgP_apply : gP v = L (v, 0) / (-a) := by
      change (-a)⁻¹ * L (v, 0) = L (v, 0) / (-a)
      rw [div_eq_mul_inv, mul_comm]
    have hgP_bound : gP v ≤ φ v - φ 0 := by
      rw [hgP_apply]
      exact (div_le_iff₀ (neg_pos.mpr ha)).2 (by simpa [mul_comm] using hsupp')
    have hreal_bound : φ 0 + gP v ≤ φ v := by
      linarith
    have hg_apply : g (y - x) = gP v := by
      simpa [g, v] using (Subspace.dualLift_of_mem (W := P) (φ := gP) v.property)
    have hxy_real : (f x).toReal + g (y - x) ≤ (f y).toReal := by
      calc
        (f x).toReal + g (y - x) = φ 0 + gP v := by
          simp [φ, g, hg_apply]
        _ ≤ φ v := hreal_bound
        _ = (f y).toReal := by
          simp [φ, v]
    have hfy_ne_bot : f y ≠ ⊥ := hne_bot_dom y hy
    have hfx_ne_top : f x ≠ ⊤ := ne_of_lt hx_dom
    have hfy_ne_top : f y ≠ ⊤ := ne_of_lt hy
    have hfx_eq : f x = (((f x).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hfx_ne_top hfx).symm
    have hfy_eq : f y = (((f y).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal hfy_ne_top hfy_ne_bot).symm
    have hxy_ereal' :
        (((f x).toReal : ℝ) : EReal) + (g (y - x) : EReal) ≤ (((f y).toReal : ℝ) : EReal) := by
      exact_mod_cast hxy_real
    have hxy_ereal : f x + (g (y - x) : EReal) ≤ f y := by
      calc
        f x + (g (y - x) : EReal) =
            (((f x).toReal : ℝ) : EReal) + (g (y - x) : EReal) := by
          rw [hfx_eq, EReal.toReal_coe]
        _ ≤ (((f y).toReal : ℝ) : EReal) := hxy_ereal'
        _ = f y := hfy_eq.symm
    exact hxy_ereal

/-- Bridge companion: a relative-interior point of `dom(f)` belongs to `dom(∂ f)`. -/
theorem mem_subdifferential_domain_of_mem_intrinsicInterior_effective_domain
    (f : E → EReal) (x : E) (hconv : is_convex_function f)
    (hx : x ∈ intrinsicInterior ℝ (effective_domain f)) :
    x ∈ subdifferential_domain f := by
  simpa [mem_subdifferential_domain] using
    subdifferential_nonempty_at_relativeInterior_point f x hconv hx

end
