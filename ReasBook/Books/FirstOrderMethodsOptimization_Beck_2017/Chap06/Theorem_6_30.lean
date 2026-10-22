/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_6
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_7
import FirstOrderMethodsOptimization_Beck_2017.Chap02.Theorem_2_2
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Definition_6_7
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Proposition_6_2_1
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_3
import FirstOrderMethodsOptimization_Beck_2017.Chap06.Theorem_6_24

-- Declarations for this item will be appended below by the statement pipeline.

universe u

noncomputable section

section

variable {E : Type u} [NormedAddCommGroup E]

recall effective_domain
recall IsProperExtendedRealFunction
recall is_convex_function
recall prox
recall projection_mapping

/-
Theorem 6.30 is `bridge/view`: the owner abstractions already fixed earlier in the chapter are
the set-valued projection map `P[...]` and the set-valued proximal map `prox[...]`. The only new
source-facing datum here is the scalar residual governing projection onto the real sublevel set
`f ⁻¹' Set.Iic (α : EReal)`, rendered without choosing a point from the proximal set before
uniqueness is available.
-/

/-- The residual function attached to the level-set projection problem. It records the optimal
function value attained by the proximal set of the scaled penalty `λ f`, shifted by the level
`α`. Under the uniqueness hypotheses used in Theorem 6.30, this coincides with the textbook
expression `φ(λ) = f (prox_{λ f} (x)) - α`. -/
def level_set_projection_residual (f : E → EReal) (α : ℝ) (x : E) (lam : ℝ) : EReal :=
  sInf (f '' prox[((lam : EReal) • f)] x) - α

-- Proof sketch: the level set `f ⁻¹' Set.Iic (α : EReal)` is contained in `effective_domain f`,
-- so this is exactly Theorem 6.24's canonical restriction theorem specialized to
-- `C = effective_domain f` and `D = f ⁻¹' Set.Iic (α : EReal)`.
/-- Theorem 6.30 (1): if the projection of `x` onto `dom(f)` exists and every such projection
point satisfies `f y ≤ α`, then the projection onto the level set
`C = f ⁻¹' Set.Iic (α : EReal)` agrees with the projection onto `dom(f)`. -/
theorem projection_mapping_sublevel_eq_projection_effective_domain_of_projection_mem_sublevel
    (f : E → EReal) (α : ℝ) (x : E)
    (hproj_nonempty : (P[effective_domain f] x).Nonempty)
    (hproj_sublevel : P[effective_domain f] x ⊆ f ⁻¹' Set.Iic (α : EReal)) :
    P[f ⁻¹' Set.Iic (α : EReal)] x = P[effective_domain f] x := by
  have hsublevel :
      f ⁻¹' Set.Iic (α : EReal) ⊆ effective_domain f := by
    intro y hy
    simpa [effective_domain] using lt_of_le_of_lt hy (show (α : EReal) < ⊤ by simp)
  simpa [Set.inter_eq_left.mpr hsublevel] using
    projection_mapping_inter_eq_of_projection_mapping_subset
      (effective_domain f) (f ⁻¹' Set.Iic (α : EReal)) x hproj_nonempty hproj_sublevel

section

variable [InnerProductSpace ℝ E] [ProperSpace E]

/-- Helper for Theorem 6.30: the real epigraph of a positively scaled function is the preimage of
the original real epigraph under the affine rescaling `(x, t) ↦ (x, t / λ)`. -/
lemma realEpigraph_scaled_function_eq_preimage_of_pos
    (f : E → EReal) (lam : PosReal) :
    realEpigraph (((lam : EReal) • f)) =
      (fun p : E × ℝ ↦ (p.1, p.2 / (lam : ℝ))) ⁻¹' realEpigraph f := by
  ext p
  simp only [realEpigraph, Set.mem_setOf_eq, Set.mem_preimage]
  constructor
  · intro hp
    -- Positive division rewrites the scaled epigraph inequality back to the original epigraph.
    rw [Pi.smul_apply, smul_eq_mul] at hp
    have hlam_pos : (0 : EReal) < (lam : ℝ) := by
      exact_mod_cast (show 0 < (lam : ℝ) from lam.2)
    have hlam_top : ((lam : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    exact (EReal.le_div_iff_mul_le hlam_pos hlam_top).2 (by simpa [mul_comm] using hp)
  · intro hp
    -- Multiplying the divided height by the positive parameter recovers the scaled inequality.
    rw [EReal.coe_div] at hp
    rw [Pi.smul_apply, smul_eq_mul]
    have hlam_pos : (0 : EReal) < (lam : ℝ) := by
      exact_mod_cast (show 0 < (lam : ℝ) from lam.2)
    have hlam_top : ((lam : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hp' := (EReal.le_div_iff_mul_le hlam_pos hlam_top).1 hp
    simpa [mul_comm] using hp'

/-- Helper for Theorem 6.30: positive scaling preserves properness, lower semicontinuity, and
convexity of an extended-real-valued function. -/
lemma scaled_function_proper_closed_convex_of_pos
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (lam : PosReal) :
    IsProperExtendedRealFunction (((lam : EReal) • f)) ∧
      LowerSemicontinuous (((lam : EReal) • f)) ∧
      is_convex_function (((lam : EReal) • f)) := by
  have hlam_nonneg : (0 : EReal) ≤ (lam : ℝ) := by
    exact_mod_cast (show 0 ≤ (lam : ℝ) by exact le_of_lt (show 0 < (lam : ℝ) from lam.2))
  have hproper : IsProperExtendedRealFunction (((lam : EReal) • f)) := by
    refine ⟨?_, ?_⟩
    · intro x
      -- Properness keeps `⊥` excluded because a positive finite scalar cannot create it.
      rw [Pi.smul_apply, smul_eq_mul]
      exact
        (EReal.mul_ne_bot _ _).2
          ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (hf_proper.ne_bot x),
            Or.inl (EReal.coe_ne_top _), Or.inl hlam_nonneg⟩
    · rcases hf_proper.effective_domain_nonempty with ⟨x, hx⟩
      -- A finite point of `f` stays finite after multiplication by a positive finite scalar.
      refine ⟨x, ?_⟩
      rw [mem_effective_domain, Pi.smul_apply, smul_eq_mul]
      exact
        lt_top_iff_ne_top.mpr <|
          (EReal.mul_ne_top _ _).2
            ⟨Or.inl (EReal.coe_ne_bot _), Or.inl hlam_nonneg,
              Or.inl (EReal.coe_ne_top _), Or.inr (mem_effective_domain.mp hx).ne⟩
  have hclosed : LowerSemicontinuous (((lam : EReal) • f)) := by
    -- Route correction: the closedness step is handled on real epigraphs, not by raw `EReal`
    -- multiplication continuity at `⊤` and `⊥`.
    rw [lowerSemicontinuous_iff_isClosed_real_epigraph]
    simpa [realEpigraph_scaled_function_eq_preimage_of_pos] using
      IsClosed.preimage (by fun_prop)
        ((lowerSemicontinuous_iff_isClosed_real_epigraph f).1 hf_closed)
  have hconvex : is_convex_function (((lam : EReal) • f)) := by
    rw [is_convex_function]
    intro p hp q hq a b ha hb hab
    have hp0 : ((lam : EReal) • f) p.1 ≤ (p.2 : EReal) := by
      simpa [Set.mem_setOf_eq] using hp
    have hq0 : ((lam : EReal) • f) q.1 ≤ (q.2 : EReal) := by
      simpa [Set.mem_setOf_eq] using hq
    have hlam_pos : (0 : EReal) < (lam : ℝ) := by
      exact_mod_cast (show 0 < (lam : ℝ) from lam.2)
    have hlam_top : ((lam : ℝ) : EReal) ≠ ⊤ := EReal.coe_ne_top _
    have hp' : (p.1, p.2 / (lam : ℝ)) ∈ {r : E × ℝ | f r.1 ≤ (r.2 : EReal)} := by
      -- Endpoint membership for the scaled epigraph is equivalent to membership in the rescaled
      -- original epigraph.
      rw [Set.mem_setOf_eq, EReal.coe_div]
      rw [Pi.smul_apply, smul_eq_mul] at hp0
      exact (EReal.le_div_iff_mul_le hlam_pos hlam_top).2 (by simpa [mul_comm] using hp0)
    have hq' : (q.1, q.2 / (lam : ℝ)) ∈ {r : E × ℝ | f r.1 ≤ (r.2 : EReal)} := by
      rw [Set.mem_setOf_eq, EReal.coe_div]
      rw [Pi.smul_apply, smul_eq_mul] at hq0
      exact (EReal.le_div_iff_mul_le hlam_pos hlam_top).2 (by simpa [mul_comm] using hq0)
    have hcombo := hf_convex hp' hq' ha hb hab
    have hdivr :
        a * (p.2 / (lam : ℝ)) + b * (q.2 / (lam : ℝ)) =
          (a * p.2 + b * q.2) / (lam : ℝ) := by
      field_simp [(show 0 < (lam : ℝ) from lam.2).ne']
    have hcombo' :
        f (a • p.1 + b • q.1) ≤ ((((a * p.2 + b * q.2) / (lam : ℝ) : ℝ)) : EReal) := by
      simpa [Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, hdivr] using hcombo
    rw [Set.mem_setOf_eq, Pi.smul_apply, smul_eq_mul]
    rw [EReal.coe_div] at hcombo'
    have hscaled := (EReal.le_div_iff_mul_le hlam_pos hlam_top).1 hcombo'
    simpa [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hscaled
  exact ⟨hproper, hclosed, hconvex⟩

/-- Helper for Theorem 6.30: subtracting a finite real constant from a finite extended-real value
agrees with subtraction in the real line after applying `toReal`. -/
lemma ereal_sub_real_eq_coe_sub {a : EReal} (ha_top : a ≠ ⊤) (ha_bot : a ≠ ⊥) (α : ℝ) :
    a - α = ((((a.toReal - α : ℝ))) : EReal) := by
  calc
    a - α = (((a.toReal : ℝ)) : EReal) - ((α : ℝ) : EReal) := by
      rw [EReal.coe_toReal ha_top ha_bot]
    _ = ((((a.toReal - α : ℝ))) : EReal) := by
      rw [← EReal.coe_sub]

/-- Helper for Theorem 6.30: once the scaled proximal set is a singleton `{u}`, the residual is
exactly `f u - α`. -/
lemma level_set_projection_residual_eq_of_scaled_prox_eq_singleton
    (f : E → EReal) (α : ℝ) (x : E) (lam : ℝ) (u : E)
    (hprox : prox[((lam : EReal) • f)] x = {u}) :
    level_set_projection_residual f α x lam = f u - α := by
  -- The residual is defined as the infimum over the proximal image, so singleton collapse gives
  -- the textbook value immediately.
  rw [level_set_projection_residual, hprox, Set.image_singleton, sInf_singleton]

/-- Helper for Theorem 6.30: every proximal point of a positively scaled proper function has
finite objective value for the original function. -/
lemma mem_effective_domain_of_mem_scaled_prox_of_pos
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x : E) (lam : PosReal)
    {u : E} (hu : u ∈ prox[((lam : EReal) • f)] x) :
    u ∈ effective_domain f := by
  rcases hf_proper.effective_domain_nonempty with ⟨u0, hu0_eff⟩
  have hu_min : ∀ v, proximal_objective (((lam : EReal) • f)) x u ≤
      proximal_objective (((lam : EReal) • f)) x v := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
    exact hu
  have hu_obj : proximal_objective (((lam : EReal) • f)) x u ≤
      proximal_objective (((lam : EReal) • f)) x u0 := hu_min u0
  have hu0_obj_top : proximal_objective (((lam : EReal) • f)) x u0 < ⊤ := by
    -- A finite comparison point in `dom f` gives a finite proximal objective for the scaled
    -- function as well.
    have hu0_val :
        f u0 = (((f u0).toReal : ℝ) : EReal) :=
      (EReal.coe_toReal (mem_effective_domain.mp hu0_eff).ne (hf_proper.ne_bot u0)).symm
    have hu0_scaled :
        (((lam : EReal) • f) u0) =
          ((((lam : ℝ) * (f u0).toReal : ℝ)) : EReal) := by
      rw [Pi.smul_apply, smul_eq_mul, hu0_val]
      simp [EReal.coe_mul]
    rw [proximal_objective_apply, hu0_scaled]
    exact EReal.add_lt_top (EReal.coe_ne_top _) (EReal.coe_ne_top _)
  have hu_obj_top : proximal_objective (((lam : EReal) • f)) x u < ⊤ :=
    lt_of_le_of_lt hu_obj hu0_obj_top
  have hu_top : f u ≠ ⊤ := by
    intro hfu
    have hmul_top : ((lam : EReal) * (f u)) = ⊤ := by
      rw [hfu]
      exact
        (EReal.mul_eq_top _ _).2
          (Or.inr <| Or.inr <| Or.inr ⟨by exact_mod_cast lam.2, rfl⟩)
    have hobj_top : proximal_objective (((lam : EReal) • f)) x u = ⊤ := by
      rw [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, hmul_top,
        EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)]
    rw [hobj_top] at hu_obj_top
    simp at hu_obj_top
  exact mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hu_top)

/-- Helper for Theorem 6.30: along positive penalty parameters, proximal points have
nonincreasing function values. -/
lemma scaled_prox_function_value_antitone_of_le
    (f : E → EReal) (hf_proper : IsProperExtendedRealFunction f) (x : E)
    (lam1 lam2 : PosReal) (hlt : (lam1 : ℝ) < (lam2 : ℝ)) {u1 u2 : E}
    (hu1 : u1 ∈ prox[((lam1 : EReal) • f)] x)
    (hu2 : u2 ∈ prox[((lam2 : EReal) • f)] x) :
    f u2 ≤ f u1 := by
  have hu1_eff : u1 ∈ effective_domain f :=
    mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam1 hu1
  have hu2_eff : u2 ∈ effective_domain f :=
    mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam2 hu2
  have hu1_min : ∀ v, proximal_objective (((lam1 : EReal) • f)) x u1 ≤
      proximal_objective (((lam1 : EReal) • f)) x v := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu1
    exact hu1
  have hu2_min : ∀ v, proximal_objective (((lam2 : EReal) • f)) x u2 ≤
      proximal_objective (((lam2 : EReal) • f)) x v := by
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu2
    exact hu2
  have hobj2 : proximal_objective (((lam2 : EReal) • f)) x u2 ≤
      proximal_objective (((lam2 : EReal) • f)) x u1 := hu2_min u1
  have hobj1 : proximal_objective (((lam1 : EReal) • f)) x u1 ≤
      proximal_objective (((lam1 : EReal) • f)) x u2 := hu1_min u2
  have hobj2_real :
      (lam2 : ℝ) * (f u2).toReal + (1 / 2 : ℝ) * ‖u2 - x‖ ^ (2 : ℕ) ≤
        (lam2 : ℝ) * (f u1).toReal + (1 / 2 : ℝ) * ‖u1 - x‖ ^ (2 : ℕ) := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, EReal.coe_mul, EReal.coe_add,
        EReal.coe_toReal (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2),
        EReal.coe_toReal (mem_effective_domain.mp hu1_eff).ne (hf_proper.ne_bot u1)] using hobj2
  have hobj1_real :
      (lam1 : ℝ) * (f u1).toReal + (1 / 2 : ℝ) * ‖u1 - x‖ ^ (2 : ℕ) ≤
        (lam1 : ℝ) * (f u2).toReal + (1 / 2 : ℝ) * ‖u2 - x‖ ^ (2 : ℕ) := by
    exact EReal.coe_le_coe_iff.mp <| by
      simpa [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, EReal.coe_mul, EReal.coe_add,
        EReal.coe_toReal (mem_effective_domain.mp hu1_eff).ne (hf_proper.ne_bot u1),
        EReal.coe_toReal (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2)] using hobj1
  have htoReal :
      (f u2).toReal ≤ (f u1).toReal := by
    nlinarith [hobj1_real, hobj2_real, hlt]
  have hcoe :
      ((((f u2).toReal : ℝ)) : EReal) ≤ ((((f u1).toReal : ℝ)) : EReal) := by
    exact_mod_cast htoReal
  simpa [EReal.coe_toReal (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2),
    EReal.coe_toReal (mem_effective_domain.mp hu1_eff).ne (hf_proper.ne_bot u1)] using hcoe

/-- Helper for Theorem 6.30: a proximal point on the active branch is a projection point onto the
sublevel set. -/
lemma mem_projection_mapping_sublevel_of_mem_scaled_prox_and_eq_level
    (f : E → EReal) (α : ℝ) (x : E) (lam : PosReal) {u : E}
    (hu : u ∈ prox[((lam : EReal) • f)] x) (hlevel : f u = (α : EReal)) :
    u ∈ P[f ⁻¹' Set.Iic (α : EReal)] x := by
  rw [mem_projection_mapping_iff]
  refine ⟨by simpa [hlevel], ?_⟩
  rw [isMinOn_iff]
  intro y hy
  have hu_min : ∀ v, proximal_objective (((lam : EReal) • f)) x u ≤
      proximal_objective (((lam : EReal) • f)) x v := by
    -- Proximal membership is exactly global optimality for the scaled proximal objective.
    rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu
    exact hu
  have hobj : proximal_objective (((lam : EReal) • f)) x u ≤
      proximal_objective (((lam : EReal) • f)) x y := hu_min y
  have hlam_real : 0 < (lam : ℝ) := lam.2
  have hscaled_le : ((lam : EReal) * f y) ≤ ((((lam : ℝ) * α : ℝ)) : EReal) := by
    -- Feasible points satisfy `f y ≤ α`, so their scaled penalty is at most `λ α`.
    calc
      (lam : EReal) * f y ≤ (lam : EReal) * (α : EReal) := by
        exact
          mul_le_mul_of_nonneg_left hy <|
            by exact_mod_cast (show 0 ≤ (lam : ℝ) by exact le_of_lt hlam_real)
      _ = ((((lam : ℝ) * α : ℝ)) : EReal) := by
        rw [EReal.coe_mul]
  have hy_obj_le : proximal_objective (((lam : EReal) • f)) x y ≤
      (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ))) : EReal) := by
    calc
      proximal_objective (((lam : EReal) • f)) x y =
          ((lam : EReal) * f y) + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
            simp [proximal_objective_apply, Pi.smul_apply, smul_eq_mul]
      _ ≤ (((((lam : ℝ) * α : ℝ)) : EReal) + ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal)) := by
            simpa [add_comm, add_left_comm, add_assoc] using
              add_le_add_left hscaled_le
                ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal)
      _ = (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ))) : EReal) := by
            simp
  have hquad_le :
      ((((1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ)) : EReal) ≤
        ((((1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ)) : EReal) := by
    have hcompare :
        (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ))) : EReal) ≤
          (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ))) : EReal) := by
      calc
        (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) : ℝ))) : EReal) =
            proximal_objective (((lam : EReal) • f)) x u := by
              simp [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, hlevel, EReal.coe_mul]
        _ ≤ proximal_objective (((lam : EReal) • f)) x y := hobj
        _ ≤ (((((lam : ℝ) * α + (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) : ℝ))) : EReal) := hy_obj_le
    -- Cancelling the common term `λ α` reduces the objective comparison to the quadratic terms.
    exact (EReal.addLECancellable_coe ((lam : ℝ) * α)).add_le_add_iff_left.mp hcompare
  have hquad_le_real :
      (1 / 2 : ℝ) * ‖u - x‖ ^ (2 : ℕ) ≤ (1 / 2 : ℝ) * ‖y - x‖ ^ (2 : ℕ) := by
    exact_mod_cast hquad_le
  have hsq : ‖u - x‖ ^ (2 : ℕ) ≤ ‖y - x‖ ^ (2 : ℕ) := by
    exact le_of_mul_le_mul_left hquad_le_real (by norm_num)
  simpa [norm_sub_rev] using (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Helper for Theorem 6.30: every real sublevel set of a convex extended-real-valued function is
convex. -/
lemma sublevel_convex_of_is_convex_function
    (f : E → EReal) (α : ℝ) (hf_convex : is_convex_function f) :
    Convex ℝ (f ⁻¹' Set.Iic (α : EReal)) := by
  intro y1 hy1 y2 hy2 a b ha hb hab
  -- The points `(y1, α)` and `(y2, α)` lie in the real epigraph, so convexity of the epigraph
  -- keeps their convex combination in the same horizontal slice.
  have hp1 : (y1, α) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simpa using hy1
  have hp2 : (y2, α) ∈ {p : E × ℝ | f p.1 ≤ (p.2 : EReal)} := by
    simpa using hy2
  have hp := hf_convex hp1 hp2 ha hb hab
  have hαr : a * α + b * α = α := by
    calc
      a * α + b * α = (a + b) * α := by ring
      _ = α := by rw [hab, one_mul]
  have hα : (((a : EReal) * α + (b : EReal) * α : EReal)) = (α : EReal) := by
    exact_mod_cast hαr
  simpa [Prod.smul_mk, Prod.mk_add_mk, hα] using hp

-- Proof sketch: formulate projection onto `C = f ⁻¹' Set.Iic (α : EReal)` as the constrained
-- quadratic minimization problem. In the positive-multiplier case, the KKT conditions identify the
-- minimizers with the proximal set of the scaled function `λ f`, while the root condition
-- `level_set_projection_residual f α x λ = 0` already forces the active constraint `f y = α`.
/-- Theorem 6.30 (2): if `λ : PosReal` is a positive root of the residual equation associated to
`C = f ⁻¹' Set.Iic (α : EReal)`, then the projection onto `C` agrees with the proximal set of the
scaled penalty `λ f`. The residual equation already encodes the active-constraint branch, so no
separate strict-sublevel witness belongs in the public statement. -/
theorem projection_mapping_sublevel_eq_scaled_prox_of_level_set_projection_residual_eq_zero
    (f : E → EReal) (α : ℝ) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f)
    (x : E) (lam : PosReal)
    (hphi : level_set_projection_residual f α x (lam : ℝ) = 0) :
    P[f ⁻¹' Set.Iic (α : EReal)] x = prox[((lam : EReal) • f)] x := by
  rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam with
    ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
  rcases prox_eq_singleton_of_proper_closed_convex (((lam : EReal) • f))
      hscaled_proper hscaled_closed hscaled_convex x with ⟨u, hprox⟩
  have hu : u ∈ prox[((lam : EReal) • f)] x := by
    simpa [hprox]
  have hu_eff : u ∈ effective_domain f :=
    mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam hu
  have hres : f u - α = 0 := by
    -- Singleton collapse identifies the residual root with the active-constraint equation.
    have hres_eq :
        level_set_projection_residual f α x (lam : ℝ) = f u - α := by
      simpa using
        level_set_projection_residual_eq_of_scaled_prox_eq_singleton f α x (lam : ℝ) u hprox
    rw [hphi] at hres_eq
    exact hres_eq.symm
  have htoReal_sub : (f u).toReal - α = 0 := by
    have hsub :
        f u - α = ((((f u).toReal - α : ℝ)) : EReal) := by
      exact ereal_sub_real_eq_coe_sub
        (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u) α
    have hcoe :
        ((((f u).toReal - α : ℝ)) : EReal) = 0 := by
      simpa [hsub] using hres
    exact_mod_cast hcoe
  have hlevel_real : (f u).toReal = α := sub_eq_zero.mp htoReal_sub
  have hlevel : f u = (α : EReal) := by
    calc
      f u = (((f u).toReal : ℝ) : EReal) := by
        exact
          (EReal.coe_toReal (mem_effective_domain.mp hu_eff).ne (hf_proper.ne_bot u)).symm
      _ = (α : EReal) := by
        exact_mod_cast hlevel_real
  have hu_proj : u ∈ P[f ⁻¹' Set.Iic (α : EReal)] x :=
    mem_projection_mapping_sublevel_of_mem_scaled_prox_and_eq_level f α x lam hu hlevel
  have hsublevel_convex : Convex ℝ (f ⁻¹' Set.Iic (α : EReal)) :=
    sublevel_convex_of_is_convex_function f α hf_convex
  -- The active-branch candidate is a projection point, and convexity makes that projection set a
  -- singleton, matching the already singleton proximal set.
  calc
    P[f ⁻¹' Set.Iic (α : EReal)] x = {u} := by
      exact Set.Subsingleton.eq_singleton_of_mem
        (projection_mapping_subsingleton (f ⁻¹' Set.Iic (α : EReal)) hsublevel_convex x) hu_proj
    _ = prox[((lam : EReal) • f)] x := hprox.symm

-- Proof sketch: let `v₁ ∈ prox[λ₁ f] x` and `v₂ ∈ prox[λ₂ f] x` with `0 ≤ λ₁ ≤ λ₂`. Compare the
-- two optimality inequalities for the proximal objectives at `v₁` and `v₂`; subtracting them
-- shows `f v₂ ≤ f v₁`. Translating by the constant level `α` gives the claimed monotonicity of
-- the residual function.
/-- Theorem 6.30 (3): the residual function `λ ↦ level_set_projection_residual f α x λ` is
nonincreasing on the nonnegative reals. -/
theorem level_set_projection_residual_antitoneOn_nonneg
    (f : E → EReal) (α : ℝ) (hf_proper : IsProperExtendedRealFunction f)
    (hf_closed : LowerSemicontinuous f) (hf_convex : is_convex_function f) (x : E) :
    AntitoneOn (level_set_projection_residual f α x) (Set.Ici 0) := by
  intro lam1 hlam1 lam2 hlam2 hle
  by_cases hlam1_zero : lam1 = 0
  · subst hlam1_zero
    by_cases hlam2_zero : lam2 = 0
    · subst hlam2_zero
      rfl
    · have hlam2_pos : 0 < lam2 := lt_of_le_of_ne hlam2 (by simpa [eq_comm] using hlam2_zero)
      let lam2Pos : PosReal := ⟨lam2, hlam2_pos⟩
      rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos
          with ⟨hscaled_proper, hscaled_closed, hscaled_convex⟩
      rcases prox_eq_singleton_of_proper_closed_convex (((lam2Pos : EReal) • f))
          hscaled_proper hscaled_closed hscaled_convex x with ⟨u2, hprox2⟩
      have hu2 : u2 ∈ prox[((lam2Pos : EReal) • f)] x := by
        simpa [hprox2]
      have hu2_eff : u2 ∈ effective_domain f :=
        mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam2Pos hu2
      have hu2_res :
          level_set_projection_residual f α x (lam2 : ℝ) = f u2 - α := by
        simpa [lam2Pos] using
          level_set_projection_residual_eq_of_scaled_prox_eq_singleton f α x (lam2 : ℝ) u2 hprox2
      have hzero_res :
          level_set_projection_residual f α x 0 = f x - α := by
        have hzero_fun : (((0 : ℝ) : EReal) • f) = 0 := by
          ext y
          simp [Pi.smul_apply, smul_eq_mul]
        rw [level_set_projection_residual, hzero_fun, prox_zero_eq_singleton x, Set.image_singleton,
          sInf_singleton]
      have hu2_le_fx : f u2 ≤ f x := by
        by_cases hfx_top : f x = ⊤
        · simpa [hfx_top] using (le_top : f u2 ≤ (⊤ : EReal))
        · have hx_eff : x ∈ effective_domain f :=
            mem_effective_domain.mpr (lt_top_iff_ne_top.mpr hfx_top)
          have hu2_min :
              ∀ v, proximal_objective (((lam2Pos : EReal) • f)) x u2 ≤
                proximal_objective (((lam2Pos : EReal) • f)) x v := by
            rw [mem_proximal_mapping_iff, isMinOn_univ_iff] at hu2
            exact hu2
          have hobj : proximal_objective (((lam2Pos : EReal) • f)) x u2 ≤
              proximal_objective (((lam2Pos : EReal) • f)) x x := hu2_min x
          have hobj_real :
              (lam2 : ℝ) * (f u2).toReal + (1 / 2 : ℝ) * ‖u2 - x‖ ^ (2 : ℕ) ≤
                (lam2 : ℝ) * (f x).toReal := by
            exact EReal.coe_le_coe_iff.mp <| by
              simpa [proximal_objective_apply, Pi.smul_apply, smul_eq_mul, EReal.coe_mul,
                EReal.coe_add,
                EReal.coe_toReal (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2),
                EReal.coe_toReal (mem_effective_domain.mp hx_eff).ne (hf_proper.ne_bot x)] using
                  hobj
          have htoReal : (f u2).toReal ≤ (f x).toReal := by
            have hquad_nonneg : 0 ≤ (1 / 2 : ℝ) * ‖u2 - x‖ ^ (2 : ℕ) := by
              positivity
            nlinarith [hobj_real, hquad_nonneg, lam2Pos.2]
          have hcoe :
              ((((f u2).toReal : ℝ)) : EReal) ≤ ((((f x).toReal : ℝ)) : EReal) := by
            exact_mod_cast htoReal
          simpa [EReal.coe_toReal (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2),
            EReal.coe_toReal (mem_effective_domain.mp hx_eff).ne (hf_proper.ne_bot x)] using hcoe
      have hsub_compare : f u2 - α ≤ f x - α := by
        by_cases hfx_top : f x = ⊤
        · rw [hfx_top]
          simp
        · have hreal :
              (f u2).toReal - α ≤ (f x).toReal - α := by
            exact sub_le_sub_right
              (EReal.toReal_le_toReal hu2_le_fx (hf_proper.ne_bot u2) hfx_top) α
          have hu2_sub :
              f u2 - α = ((((f u2).toReal - α : ℝ)) : EReal) := by
            exact ereal_sub_real_eq_coe_sub
              (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2) α
          have hx_sub :
              f x - α = ((((f x).toReal - α : ℝ)) : EReal) := by
            exact ereal_sub_real_eq_coe_sub hfx_top (hf_proper.ne_bot x) α
          have hcoe :
              ((((f u2).toReal - α : ℝ)) : EReal) ≤
                ((((f x).toReal - α : ℝ)) : EReal) := by
            exact_mod_cast hreal
          simpa [hu2_sub, hx_sub] using hcoe
      calc
        level_set_projection_residual f α x lam2 = f u2 - α := hu2_res
        _ ≤ f x - α := hsub_compare
        _ = level_set_projection_residual f α x 0 := hzero_res.symm
  · have hlam1_pos : 0 < lam1 := lt_of_le_of_ne hlam1 (by simpa [eq_comm] using hlam1_zero)
    have hlam2_pos : 0 < lam2 := lt_of_lt_of_le hlam1_pos hle
    let lam1Pos : PosReal := ⟨lam1, hlam1_pos⟩
    let lam2Pos : PosReal := ⟨lam2, hlam2_pos⟩
    by_cases hEq : lam1 = lam2
    · subst hEq
      rfl
    rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam1Pos
        with ⟨hscaled1_proper, hscaled1_closed, hscaled1_convex⟩
    rcases scaled_function_proper_closed_convex_of_pos f hf_proper hf_closed hf_convex lam2Pos
        with ⟨hscaled2_proper, hscaled2_closed, hscaled2_convex⟩
    rcases prox_eq_singleton_of_proper_closed_convex (((lam1Pos : EReal) • f))
        hscaled1_proper hscaled1_closed hscaled1_convex x with ⟨u1, hprox1⟩
    rcases prox_eq_singleton_of_proper_closed_convex (((lam2Pos : EReal) • f))
        hscaled2_proper hscaled2_closed hscaled2_convex x with ⟨u2, hprox2⟩
    have hu1 : u1 ∈ prox[((lam1Pos : EReal) • f)] x := by
      simpa [hprox1]
    have hu2 : u2 ∈ prox[((lam2Pos : EReal) • f)] x := by
      simpa [hprox2]
    have hu1_eff : u1 ∈ effective_domain f :=
      mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam1Pos hu1
    have hu2_eff : u2 ∈ effective_domain f :=
      mem_effective_domain_of_mem_scaled_prox_of_pos f hf_proper x lam2Pos hu2
    have hres1 :
        level_set_projection_residual f α x lam1 = f u1 - α := by
      simpa [lam1Pos] using
        level_set_projection_residual_eq_of_scaled_prox_eq_singleton f α x lam1 u1 hprox1
    have hres2 :
        level_set_projection_residual f α x lam2 = f u2 - α := by
      simpa [lam2Pos] using
        level_set_projection_residual_eq_of_scaled_prox_eq_singleton f α x lam2 u2 hprox2
    have hlt : (lam1 : ℝ) < (lam2 : ℝ) := lt_of_le_of_ne hle hEq
    have hfu_antitone : f u2 ≤ f u1 :=
      scaled_prox_function_value_antitone_of_le f hf_proper x lam1Pos lam2Pos hlt hu1 hu2
    have hsub_compare : f u2 - α ≤ f u1 - α := by
      have hreal :
          (f u2).toReal - α ≤ (f u1).toReal - α := by
        exact sub_le_sub_right
          (EReal.toReal_le_toReal hfu_antitone (hf_proper.ne_bot u2)
            (mem_effective_domain.mp hu1_eff).ne) α
      have hu2_sub :
          f u2 - α = ((((f u2).toReal - α : ℝ)) : EReal) := by
        exact ereal_sub_real_eq_coe_sub
          (mem_effective_domain.mp hu2_eff).ne (hf_proper.ne_bot u2) α
      have hu1_sub :
          f u1 - α = ((((f u1).toReal - α : ℝ)) : EReal) := by
        exact ereal_sub_real_eq_coe_sub
          (mem_effective_domain.mp hu1_eff).ne (hf_proper.ne_bot u1) α
      have hcoe :
          ((((f u2).toReal - α : ℝ)) : EReal) ≤
            ((((f u1).toReal - α : ℝ)) : EReal) := by
        exact_mod_cast hreal
      simpa [hu2_sub, hu1_sub] using hcoe
    calc
      level_set_projection_residual f α x lam2 = f u2 - α := hres2
      _ ≤ f u1 - α := hsub_compare
      _ = level_set_projection_residual f α x lam1 := hres1.symm

end

end
