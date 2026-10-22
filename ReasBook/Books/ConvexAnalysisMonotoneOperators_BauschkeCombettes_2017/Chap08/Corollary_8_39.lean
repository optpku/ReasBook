/-
Authors: Yifan Bai, Zichen Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap01.Lemma_1_44
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Proposition_8_11
import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap08.Theorem_8_38

-- Declarations for this item will be appended below by the statement pipeline.

open Set
open scoped Topology

universe u

namespace ERealFunction

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 8.39: outside the effective domain of an `]-∞,+∞]`-valued function, the
value is necessarily `⊤`. -/
private theorem value_eq_top_of_not_mem_effectiveDomain
    {f : H → Set.Ioi (⊥ : EReal)} {x : H} (hx : x ∉ effectiveDomain f) :
    (f x : EReal) = ⊤ := by
  -- A finite value would put the point back into the effective domain.
  by_contra htop
  exact hx (mem_effectiveDomain_iff.mpr (lt_of_le_of_ne le_top htop))

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 8.39: away from the closure of the effective domain, the coerced
`EReal`-valued map is locally constant equal to `⊤`, hence continuous. -/
private theorem continuousAt_of_not_mem_closure_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal)) {x : H} (hx : x ∉ closure (effectiveDomain f)) :
    ContinuousAt (fun y : H ↦ (f y : EReal)) x := by
  have hnhds :
      (closure (effectiveDomain f))ᶜ ∈ 𝓝 x :=
    isClosed_closure.isOpen_compl.mem_nhds hx
  have hconst :
      (fun y : H ↦ (f y : EReal)) =ᶠ[𝓝 x] fun _ : H ↦ (⊤ : EReal) := by
    -- On the complement of the closure, points are outside the effective domain, so the function
    -- stays on its `+∞` branch.
    filter_upwards [hnhds] with y hy
    have hy_not_mem : y ∉ effectiveDomain f := by
      intro hy_mem
      exact hy (subset_closure hy_mem)
    simp [value_eq_top_of_not_mem_effectiveDomain hy_not_mem]
  -- Eventual equality with the constant `⊤` function transfers continuity.
  simpa using (continuousAt_const : ContinuousAt (fun _ : H ↦ (⊤ : EReal)) x).congr hconst.symm

omit [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 8.39: every point outside the closure of the effective domain belongs to
the continuity set of the coerced `EReal`-valued map. -/
private theorem compl_closure_effectiveDomain_subset_continuityPoints
    (f : H → Set.Ioi (⊥ : EReal)) :
    (closure (effectiveDomain f))ᶜ ⊆ {x : H | ContinuousAt (fun y : H ↦ (f y : EReal)) x} := by
  -- Apply the local-constancy lemma pointwise on the open exterior of the effective domain.
  intro x hx
  exact continuousAt_of_not_mem_closure_effectiveDomain f hx

/-- Helper for Corollary 8.39: the finite value `0` belongs to `]-∞,+∞]`. -/
private theorem zero_mem_Ioi_bot : (0 : EReal) ∈ Set.Ioi (⊥ : EReal) :=
  EReal.bot_lt_coe 0

/-- Helper for Corollary 8.39: the value `+∞` also belongs to `]-∞,+∞]`. -/
private theorem top_mem_Ioi_bot_local : (⊤ : EReal) ∈ Set.Ioi (⊥ : EReal) := by
  -- Membership in `]-∞,+∞]` is exactly the strict inequality `⊥ < ⊤`.
  simp

/-- Helper for Corollary 8.39: the indicator of the positive ray takes the value `0` on
`(0, +∞)` and `+∞` elsewhere. This is the concrete witness showing that the current theorem
statement uses the wrong continuity notion. -/
private noncomputable def positiveRayIndicator : ℝ → Set.Ioi (⊥ : EReal) :=
  fun x ↦
    if 0 < x then
      ⟨(0 : EReal), zero_mem_Ioi_bot⟩
    else
      ⟨(⊤ : EReal), top_mem_Ioi_bot_local⟩

/-- Helper for Corollary 8.39: on the positive ray, the witness function is the finite constant
`0`. -/
@[simp] private theorem positiveRayIndicator_apply_of_pos {x : ℝ} (hx : 0 < x) :
    (positiveRayIndicator x : EReal) = 0 := by
  -- The positive branch of the definition is exactly the constant finite value `0`.
  simp [positiveRayIndicator, hx]

/-- Helper for Corollary 8.39: on the nonpositive ray, the witness function is constantly `+∞`. -/
@[simp] private theorem positiveRayIndicator_apply_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    (positiveRayIndicator x : EReal) = ⊤ := by
  -- The complementary branch of the definition is definitionally the constant `⊤`.
  simp [positiveRayIndicator, not_lt.mpr hx]

/-- Helper for Corollary 8.39: the effective domain of the positive-ray witness is exactly
`(0, +∞)`. -/
@[simp] private theorem effectiveDomain_positiveRayIndicator :
    effectiveDomain positiveRayIndicator = Set.Ioi (0 : ℝ) := by
  -- Finite values occur exactly on the positive branch of the definition.
  ext x
  constructor
  · intro hx
    rw [mem_effectiveDomain_iff] at hx
    by_contra hx_nonpos
    rw [positiveRayIndicator_apply_of_nonpos (not_lt.mp hx_nonpos)] at hx
    exact lt_irrefl _ hx
  · intro hx
    rw [mem_effectiveDomain_iff, positiveRayIndicator_apply_of_pos hx]
    exact EReal.coe_lt_top 0

/-- Helper for Corollary 8.39: the positive-ray witness is convex on its effective domain because
it is constant there. -/
private theorem positiveRayIndicator_convexOn_effectiveDomain :
    ConvexOn positiveRayIndicator (effectiveDomain positiveRayIndicator) := by
  refine ⟨?_, subset_rfl, ?_⟩
  · -- The effective domain is nonempty because, for instance, `1` lies in `(0, +∞)`.
    refine ⟨1, ?_⟩
    simp [effectiveDomain_positiveRayIndicator]
  · intro x hx y hy α hα0 hα1
    have hx_pos : 0 < x := by
      simpa [effectiveDomain_positiveRayIndicator] using hx
    have hy_pos : 0 < y := by
      simpa [effectiveDomain_positiveRayIndicator] using hy
    have h_one_sub_pos : 0 < 1 - α := by
      linarith
    have hcombo_pos : 0 < α • x + (1 - α) • y := by
      have hcombo_mul : 0 < α * x + (1 - α) * y := by
        nlinarith
      simpa [smul_eq_mul] using hcombo_mul
    -- Every relevant value is `0`, so Jensen's inequality is an equality.
    rw [positiveRayIndicator_apply_of_pos hcombo_pos, positiveRayIndicator_apply_of_pos hx_pos,
      positiveRayIndicator_apply_of_pos hy_pos]
    simp

/-- Helper for Corollary 8.39: the positive-ray witness satisfies the finite-dimensional branch of
the theorem hypotheses. -/
private theorem positiveRayIndicator_satisfies_hypotheses :
    (∃ x : ℝ, ∃ ρ : ℝ, 0 < ρ ∧
      sSup ((fun y : ℝ ↦ (positiveRayIndicator y : EReal)) '' Metric.ball x ρ) < ⊤) ∨
      LowerSemicontinuous (fun x : ℝ ↦ (positiveRayIndicator x : EReal)) ∨
      FiniteDimensional ℝ ℝ := by
  -- The ambient space `ℝ` is finite-dimensional, so the third branch holds immediately.
  exact Or.inr (Or.inr inferInstance)

/-- Helper for Corollary 8.39: the witness is continuous at `-1` because the function is locally
constant equal to `⊤` on a neighborhood disjoint from the closure of its effective domain. -/
private theorem positiveRayIndicator_continuousAt_negOne :
    ContinuousAt (fun y : ℝ ↦ (positiveRayIndicator y : EReal)) (-1 : ℝ) := by
  -- The point `-1` lies outside `closure (0, +∞) = [0, +∞)`, so the generic exterior continuity
  -- lemma applies.
  apply continuousAt_of_not_mem_closure_effectiveDomain positiveRayIndicator
  simp [effectiveDomain_positiveRayIndicator, closure_Ioi]

/-- Helper for Corollary 8.39: the point `-1` does not belong to the interior of the witness
effective domain. -/
private theorem negOne_not_mem_interior_effectiveDomain_positiveRayIndicator :
    (-1 : ℝ) ∉ interior (effectiveDomain positiveRayIndicator) := by
  -- The effective domain is `(0, +∞)`, whose interior is itself.
  simp [effectiveDomain_positiveRayIndicator, interior_Ioi]

/-- Helper for Corollary 8.39: the current theorem header is false for the explicit positive-ray
witness on `ℝ`. -/
private theorem positiveRayIndicator_counterexample :
    {x : ℝ | ContinuousAt (fun y ↦ (positiveRayIndicator y : EReal)) x} ≠
      interior (effectiveDomain positiveRayIndicator) := by
  -- The witness point `-1` belongs to the left-hand side but not to the right-hand side.
  intro hEq
  have hcont : (-1 : ℝ) ∈ {x : ℝ | ContinuousAt (fun y ↦ (positiveRayIndicator y : EReal)) x} := by
    exact positiveRayIndicator_continuousAt_negOne
  have hnot : (-1 : ℝ) ∉ interior (effectiveDomain positiveRayIndicator) :=
    negOne_not_mem_interior_effectiveDomain_positiveRayIndicator
  exact hnot (hEq ▸ hcont)

omit [CompleteSpace H] in
/-- Helper for Corollary 8.39: convexity on the effective domain forces the effective domain
itself to be convex. -/
private theorem convex_effectiveDomain_of_convexOn
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    Convex ℝ (effectiveDomain f) := by
  -- A convex combination of finite endpoint values is still finite, so the combination stays in
  -- the effective domain.
  rw [convex_iff_forall_pos]
  intro x hx y hy a b ha hb hab
  have ha_lt_one : a < 1 := by
    linarith
  have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
    rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
  have hb_eq : (1 - a : ℝ) = b := by
    linarith
  have hineq0 := hconv.ineq hx hy ha ha_lt_one
  have hineq1 :
      (f (a • x + (1 - a) • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
    simpa [hsub_cast] using hineq0
  have hineq :
      (f (a • x + b • y) : EReal) ≤
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
    simpa [hb_eq] using hineq1
  have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
  have hx_bot : (f x : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
  have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
  have hy_bot : (f y : EReal) ≠ ⊥ := by
    exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
  have hsum :
      (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
        ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
    rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    simp
  rw [mem_effectiveDomain_iff]
  exact lt_of_le_of_lt (hineq.trans_eq hsum) (EReal.coe_lt_top _)

omit [CompleteSpace H] in
/-- Helper for Corollary 8.39: the finite real representative is convex on the effective domain. -/
private theorem toReal_convexOn_effectiveDomain
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f)) :
    _root_.ConvexOn ℝ (effectiveDomain f) (fun x ↦ (f x : EReal).toReal) := by
  -- Rewrite the extended-real Jensen inequality through `toReal` on finite-domain points.
  rw [convexOn_iff_forall_pos]
  constructor
  · exact convex_effectiveDomain_of_convexOn f hconv
  · intro x hx y hy a b ha hb hab
    have ha_lt_one : a < 1 := by
      linarith
    have hsub_cast : (((1 - a : ℝ) : EReal)) = 1 - (a : EReal) := by
      rw [show (1 : EReal) = ((1 : ℝ) : EReal) by norm_num, ← EReal.coe_sub]
    have hb_eq : (1 - a : ℝ) = b := by
      linarith
    have hineq0 := hconv.ineq hx hy ha ha_lt_one
    have hineq1 :
        (f (a • x + (1 - a) • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (((1 - a : ℝ) : EReal) * (f y : EReal)) := by
      simpa [hsub_cast] using hineq0
    have hineq :
        (f (a • x + b • y) : EReal) ≤
          (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) := by
      simpa [hb_eq] using hineq1
    have hxy : a • x + b • y ∈ effectiveDomain f :=
      (convex_effectiveDomain_of_convexOn f hconv) hx hy ha.le hb.le hab
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    have hy_top : (f y : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hy)
    have hy_bot : (f y : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f y : EReal) from (f y).2)
    have hxy_bot : (f (a • x + b • y) : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f (a • x + b • y) : EReal) from
        (f (a • x + b • y)).2)
    have hsum :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) =
          ((a * (f x : EReal).toReal + b * (f y : EReal).toReal : ℝ) : EReal) := by
      rw [← EReal.coe_toReal hx_top hx_bot, ← EReal.coe_toReal hy_top hy_bot,
        ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
      simp
    have hright_top :
        (a : EReal) * (f x : EReal) + (b : EReal) * (f y : EReal) ≠ ⊤ := by
      rw [hsum]
      exact ne_of_lt (EReal.coe_lt_top _)
    simpa [hsum] using EReal.toReal_le_toReal hineq hxy_bot hright_top

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] in
/-- Helper for Corollary 8.39: the effective domain is the union of the finite real lower level
sets indexed by naturals. -/
private theorem effectiveDomain_eq_iUnion_levelSet_nat
    (f : H → Set.Ioi (⊥ : EReal)) :
    effectiveDomain f = ⋃ n : ℕ, {x : H | (f x : EReal) ≤ ((n : ℝ) : EReal)} := by
  -- Every finite extended-real value is bounded above by some natural number, and each such lower
  -- level set is automatically contained in the finite-value domain.
  ext x
  constructor
  · intro hx
    have hx_top : (f x : EReal) ≠ ⊤ := ne_of_lt (mem_effectiveDomain_iff.mp hx)
    have hx_bot : (f x : EReal) ≠ ⊥ := by
      exact ne_of_gt (show (⊥ : EReal) < (f x : EReal) from (f x).2)
    obtain ⟨n, hn⟩ := exists_nat_ge ((f x : EReal).toReal)
    refine mem_iUnion.mpr ⟨n, ?_⟩
    change (f x : EReal) ≤ ((n : ℝ) : EReal)
    rw [show (f x : EReal) = (((f x : EReal).toReal : ℝ) : EReal) by
      exact (EReal.coe_toReal hx_top hx_bot).symm]
    exact_mod_cast hn
  · intro hx
    rcases mem_iUnion.mp hx with ⟨n, hn⟩
    rw [mem_effectiveDomain_iff]
    exact lt_of_le_of_lt hn (EReal.coe_lt_top (n : ℝ))

omit [CompleteSpace H] in
/-- Helper for Corollary 8.39: one finite-sup ball suffices to obtain local-domain continuity at
any interior-domain point via Theorem 8.38. -/
private theorem exists_local_domain_continuity_of_finiteSupBall
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    {x₀ : H}
    (hfinite : ∃ ρ > 0, sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤)
    {x : H} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
      ContinuousAt (fun y ↦ (f y : EReal).toReal) x := by
  -- Theorem 8.38 upgrades a finite-sup ball to a local Lipschitz estimate on the full interior of
  -- the effective domain.
  rcases convex_locallyLipschitzNear_on_interior_of_finiteSupBall (x₀ := x₀) f hconv hfinite x hx
    with ⟨β, ρ, hρ, hball, hLip⟩
  refine ⟨ρ, hρ, hball, ?_⟩
  exact hLip.continuousOn.continuousAt (Metric.ball_mem_nhds x hρ)

omit [InnerProductSpace ℝ H] in
/-- Helper for Corollary 8.39: lower semicontinuity produces a lower level set with nonempty
interior, hence a ball on which the function has finite supremum. -/
private theorem exists_finiteSupBall_of_lowerSemicontinuous
    (f : H → Set.Ioi (⊥ : EReal))
    (hlsc : LowerSemicontinuous (fun x : H ↦ (f x : EReal)))
    {x : H} (hx : x ∈ interior (effectiveDomain f)) :
    ∃ x₀ : H, ∃ ρ : ℝ, 0 < ρ ∧
      sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball x₀ ρ) < ⊤ := by
  let C : ℕ → Set H := fun n ↦ {y : H | (f y : EReal) ≤ ((n : ℝ) : EReal)}
  have hclosed : ∀ n, IsClosed (C n) := by
    -- Lower semicontinuity makes each lower level set closed.
    intro n
    simpa [C] using hlsc.isClosed_preimage (((n : ℝ) : EReal))
  have hcover := effectiveDomain_eq_iUnion_levelSet_nat f
  have hx_closure : x ∈ closure (⋃ n : ℕ, interior (C n)) := by
    -- Ursescu's lemma transfers nonempty interior from the domain to one lower level set.
    rw [(lemma_1_44 (X := H)).1 C hclosed, ← hcover]
    exact subset_closure hx
  have hnonempty : (⋃ n : ℕ, interior (C n)).Nonempty := by
    by_contra hempty
    have hempty_eq : (⋃ n : ℕ, interior (C n)) = ∅ := Set.not_nonempty_iff_eq_empty.mp hempty
    have : x ∈ closure (∅ : Set H) := by
      simpa [hempty_eq] using hx_closure
    have : False := by
      simpa using this
    exact this.elim
  rcases hnonempty with ⟨x₀, hx₀⟩
  rcases mem_iUnion.mp hx₀ with ⟨n, hn⟩
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hn) with ⟨ρ, hρ, hball⟩
  refine ⟨x₀, ρ, hρ, ?_⟩
  -- A ball contained in `C n` has all values bounded above by the finite level `n`.
  refine lt_of_le_of_lt ?_ (EReal.coe_lt_top (n : ℝ))
  refine sSup_le ?_
  rintro _ ⟨y, hy, rfl⟩
  exact hball hy

-- Proof sketch: the inclusion from continuity points to `interior (effectiveDomain f)` is the
-- general extended-real continuity fact. For the reverse inclusion, apply Theorem 8.38 under
-- hypothesis (i); under hypothesis (ii), use lower semicontinuity to find a nonempty interior
-- lower level set and reduce to (i); under hypothesis (iii), use finite dimensionality together
-- with Proposition 8.11 to bound `f` above on a ball and again reduce to (i).
/-- Corollary 8.39: for a proper convex `]-∞,+∞]`-valued function on a real Hilbert space, if it is bounded above on some
open ball, or is lower semicontinuous, or the ambient space is finite-dimensional, then the points
where the finite real representative is continuous on a neighborhood contained in the effective
domain are exactly the interior of the effective domain. -/
-- Route correction: the current Lean statement is not the textbook continuity theorem. On
-- `H = ℝ`, the indicator of a ray is convex on its effective domain and satisfies the
-- finite-dimensional branch, but the coerced `EReal`-valued map is continuous at exterior points
-- where it is locally constant `⊤`. The textbook `cont f` only counts finite-domain continuity.
theorem continuous_points_eq_interior_effectiveDomain_of_convexOn_of_finiteSupBall_or_lowerSemicontinuous_or_finiteDimensional
    (f : H → Set.Ioi (⊥ : EReal))
    (hconv : ConvexOn f (effectiveDomain f))
    (h :
      (∃ x : H, ∃ ρ : ℝ, 0 < ρ ∧
        sSup ((fun y : H ↦ (f y : EReal)) '' Metric.ball x ρ) < ⊤) ∨
      LowerSemicontinuous (fun x : H ↦ (f x : EReal)) ∨
      FiniteDimensional ℝ H) :
    {x : H | ∃ ρ : ℝ, 0 < ρ ∧ Metric.ball x ρ ⊆ effectiveDomain f ∧
      ContinuousAt (fun y : H ↦ (f y : EReal).toReal) x} = interior (effectiveDomain f) := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨ρ, hρ, hball, hcont⟩
    -- A neighborhood ball contained in the effective domain is exactly the interior witness.
    rw [mem_interior_iff_mem_nhds]
    exact Filter.mem_of_superset (Metric.ball_mem_nhds x hρ) hball
  · intro hx
    rcases h with hfinite | hlsc | hfd
    · rcases hfinite with ⟨x₀, ρ₀, hρ₀, hsup₀⟩
      -- Branch (i): invoke Theorem 8.38 directly from the given finite-sup ball.
      exact exists_local_domain_continuity_of_finiteSupBall f hconv ⟨ρ₀, hρ₀, hsup₀⟩ hx
    · rcases exists_finiteSupBall_of_lowerSemicontinuous f hlsc hx with ⟨x₀, ρ₀, hρ₀, hsup₀⟩
      -- Branch (ii): reduce lower semicontinuity to branch (i) through a lower level set.
      exact exists_local_domain_continuity_of_finiteSupBall f hconv ⟨ρ₀, hρ₀, hsup₀⟩ hx
    · rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx) with ⟨ρ, hρ, hball⟩
      refine ⟨ρ, hρ, hball, ?_⟩
      -- Branch (iii): finite-dimensional convex real functions are continuous on the interior of
      -- their convex domain, so the repaired local-domain continuity statement follows directly.
      have hcontOn : ContinuousOn (fun y ↦ (f y : EReal).toReal) (interior (effectiveDomain f)) := by
        exact (_root_.ConvexOn.continuousOn_interior (toReal_convexOn_effectiveDomain f hconv))
      exact hcontOn.continuousAt (isOpen_interior.mem_nhds hx)

end ERealFunction
