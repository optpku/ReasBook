/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.InnerProductSpace.ProdL2
import OptimizationTheoryAndMethods_SunYuan_2006.Chap01.Theorem_1_3_24
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Algorithm_14_4_1

noncomputable section

section

variable {n : ℕ}

local notation "Point" => EuclideanSpace ℝ (Fin n)

-- Layer triage:
-- * core/canonical: `subdifferential`, `cuttingPlaneAffineMinorant`
-- * source-facing: `convexOn_eq_sSup_subgradientAffineSupportValue`
-- * bridge/view: `subgradientAffineSupportValueSet`

/-- The support values `f y + ⟪g, x - y⟫` obtained from Euclidean subgradients `g` at the base
point `y`, evaluated at `x`. -/
def subgradientAffineSupportValueSet (f : Point → ℝ) (x y : Point) : Set ℝ :=
  {r | ∃ g : Point, Chapter14.IsSubgradientAt f y g ∧ cuttingPlaneAffineMinorant f y g x = r}

/-- Membership in `subgradientAffineSupportValueSet f x y` is exactly the existence of a
Euclidean subgradient at `y` realizing the support value `r = f y + ⟪g, x - y⟫`. -/
theorem mem_subgradientAffineSupportValueSet_iff
    (f : Point → ℝ) (x y : Point) (r : ℝ) :
    r ∈ subgradientAffineSupportValueSet f x y ↔
      ∃ g : Point, Chapter14.IsSubgradientAt f y g ∧ f y + inner ℝ g (x - y) = r := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    -- Unfold the affine minorant to expose the source expression `f y + ⟪g, x - y⟫`.
    refine ⟨g, hg, ?_⟩
    rw [cuttingPlaneAffineMinorant_apply]
  · rintro ⟨g, hg, hr⟩
    -- Repackage the explicit support value as a member of the support-value set.
    refine ⟨g, hg, ?_⟩
    rwa [cuttingPlaneAffineMinorant_apply]

/-- Helper for Chapter14 Exercise 14.6: the graph point `(x, f x)` lies on the frontier of the
lifted epigraph `{p | f p.fst ≤ p.snd}` in the `L²` product space. -/
lemma mem_frontier_epigraph_univ_point
    (f : Point → ℝ) (x : Point) :
    WithLp.toLp 2 (x, f x) ∈
      frontier ({p : WithLp 2 (Point × ℝ) | f p.fst ≤ p.snd} : Set (WithLp 2 (Point × ℝ))) := by
  let S : Set (WithLp 2 (Point × ℝ)) := {p | f p.fst ≤ p.snd}
  have hx_mem : WithLp.toLp 2 (x, f x) ∈ S := by
    -- The point `(x, f x)` lies on the graph itself, hence in the lifted epigraph.
    simp [S]
  rw [mem_frontier_iff_notMem_interior hx_mem]
  intro hx_int
  rcases Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx_int) with ⟨ε, hε, hball⟩
  let q : WithLp 2 (Point × ℝ) := WithLp.toLp 2 (x, f x - ε / 2)
  have hq_mem_ball : q ∈ Metric.ball (WithLp.toLp 2 (x, f x)) ε := by
    -- Move only in the vertical direction; the `L²` product distance is then just the real gap.
    rw [Metric.mem_ball]
    dsimp [q]
    rw [dist_eq_norm, ← WithLp.toLp_sub, Prod.mk_sub_mk, sub_self, WithLp.norm_toLp_snd,
      Real.norm_eq_abs]
    have hEq : (f x - ε / 2) - f x = -(ε / 2) := by
      ring
    rw [hEq, abs_of_nonpos]
    · linarith
    · linarith
  have hq_mem : q ∈ S := hball hq_mem_ball
  have hq_not_mem : q ∉ S := by
    -- The vertical perturbation moves strictly below the epigraph boundary at `x`.
    intro hqS
    have : f x ≤ f x - ε / 2 := by
      simpa [S, q] using hqS
    linarith
  exact hq_not_mem hq_mem

/-- Helper for Chapter14 Exercise 14.6: a convex function on all of `ℝ^n` admits a Euclidean
subgradient at every point. -/
lemma exists_subgradientAt_of_convexOn
    (f : Point → ℝ) (h_convex : ConvexOn ℝ Set.univ f) (x : Point) :
    ∃ g : Point, Chapter14.IsSubgradientAt f x g := by
  let S : Set (WithLp 2 (Point × ℝ)) := {p | f p.fst ≤ p.snd}
  let xbar : WithLp 2 (Point × ℝ) := WithLp.toLp 2 (x, f x)
  have hS_convex : Convex ℝ S := by
    -- Convexity of the lifted epigraph is just the source convexity inequality on the height.
    intro p hp q hq a b ha hb hab
    have hp' : f p.fst ≤ p.snd := by
      simpa [S] using hp
    have hq' : f q.fst ≤ q.snd := by
      simpa [S] using hq
    change f (a • p.fst + b • q.fst) ≤ (a • p + b • q).snd
    calc
      f (a • p.fst + b • q.fst) ≤ a * f p.fst + b * f q.fst := by
        simpa using h_convex.2 (by simp) (by simp) ha hb hab
      _ ≤ a * p.snd + b * q.snd := by
        gcongr
      _ = (a • p + b • q).snd := by
        simp
  have hxbar_frontier : xbar ∈ frontier S := by
    -- The graph point is a boundary point of the epigraph.
    simpa [S, xbar] using mem_frontier_epigraph_univ_point f x
  rcases existsNonzeroSupportingVectorOnClosure S hS_convex xbar hxbar_frontier with
      ⟨normal, hnormal_ne, hclosure⟩
  have hnormal_snd_ne : normal.snd ≠ 0 := by
    -- If the scalar component vanished, the support inequality would force the horizontal normal
    -- to vanish as well, contradicting that the supporting vector is nonzero.
    intro hzero
    have hle_all : ∀ z : Point, inner ℝ normal.fst z ≤ inner ℝ normal.fst x := by
      intro z
      have hz_mem : WithLp.toLp 2 (z, f z) ∈ S := by
        simp [S]
      have hz_closure : WithLp.toLp 2 (z, f z) ∈ closure S := subset_closure hz_mem
      have hz_halfspace := hclosure hz_closure
      simpa [xbar, hzero, S, WithLp.prod_inner_apply, add_comm, add_left_comm, add_assoc] using
        hz_halfspace
    have hnorm_sq_nonpos : ‖normal.fst‖ ^ 2 ≤ 0 := by
      have hplus := hle_all (x + normal.fst)
      simpa [inner_add_right, inner_self_eq_norm_sq_to_K, add_comm, add_left_comm, add_assoc] using
        hplus
    have hnorm_zero : ‖normal.fst‖ = 0 := by
      nlinarith [hnorm_sq_nonpos, sq_nonneg ‖normal.fst‖]
    have hfst_zero : normal.fst = 0 := norm_eq_zero.mp hnorm_zero
    have hof : WithLp.ofLp normal = (0 : Point × ℝ) := by
      ext <;> simp [hfst_zero, hzero]
    have hnormal_zero : normal = 0 := by
      simpa using congrArg (WithLp.toLp 2) hof
    exact hnormal_ne hnormal_zero
  have hnormal_snd_nonpos : normal.snd ≤ 0 := by
    -- The epigraph contains points arbitrarily above `(x, f x)`, so the supporting normal must
    -- point downward in the scalar direction.
    have hxup_mem : WithLp.toLp 2 (x, f x + 1) ∈ S := by
      simp [S]
    have hxup_halfspace : (f x + 1) * normal.snd ≤ f x * normal.snd := by
      simpa [xbar, WithLp.prod_inner_apply, add_comm, add_left_comm, add_assoc] using
        hclosure (subset_closure hxup_mem)
    linarith
  have hnormal_snd_neg : normal.snd < 0 := by
    exact lt_of_le_of_ne hnormal_snd_nonpos hnormal_snd_ne
  let g : Point := (1 / (-normal.snd)) • normal.fst
  refine ⟨g, (Chapter14.isSubgradientAt_iff f x g).2 ?_⟩
  intro z
  have hz_mem : WithLp.toLp 2 (z, f z) ∈ S := by
    simp [S]
  have hz_halfspace := hclosure (subset_closure hz_mem)
  have hz_support :
      inner ℝ normal.fst z + f z * normal.snd ≤ inner ℝ normal.fst x + f x * normal.snd := by
    -- Evaluate the supporting half-space inequality on the graph point `(z, f z)`.
    simpa [xbar, WithLp.prod_inner_apply, add_comm, add_left_comm, add_assoc] using hz_halfspace
  have hz_inner : inner ℝ normal.fst (z - x) = inner ℝ normal.fst z - inner ℝ normal.fst x := by
    rw [inner_sub_right]
  have hz_bound : inner ℝ normal.fst (z - x) ≤ (-normal.snd) * (f z - f x) := by
    -- Rearranging the half-space inequality isolates the horizontal support term.
    nlinarith [hz_support, hz_inner]
  have hpos : 0 < -normal.snd := by
    linarith
  have hz_div : inner ℝ normal.fst (z - x) / (-normal.snd) ≤ f z - f x := by
    -- Divide by the positive quantity `-normal.snd` to recover the affine minorant slope.
    exact (div_le_iff₀ hpos).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hz_bound)
  have hz_minorant : inner ℝ g (z - x) ≤ f z - f x := by
    change inner ℝ ((1 / (-normal.snd)) • normal.fst) (z - x) ≤ f z - f x
    rw [inner_smul_left]
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hz_div
  linarith

/-- Helper for Chapter14 Exercise 14.6: every support value generated from a subgradient at `y`
is bounded above by `f x`. -/
lemma sSup_subgradientAffineSupportValueSet_le
    (f : Point → ℝ) (h_convex : ConvexOn ℝ Set.univ f) (x y : Point) :
    sSup (subgradientAffineSupportValueSet f x y) ≤ f x := by
  rcases exists_subgradientAt_of_convexOn f h_convex y with ⟨g0, hg0⟩
  have h_nonempty : (subgradientAffineSupportValueSet f x y).Nonempty := by
    refine ⟨cuttingPlaneAffineMinorant f y g0 x, ?_⟩
    exact ⟨g0, hg0, rfl⟩
  exact csSup_le h_nonempty (by
    intro r hr
    rcases (mem_subgradientAffineSupportValueSet_iff f x y r).1 hr with ⟨g, hg, hgr⟩
    rw [← hgr]
    simpa using (Chapter14.isSubgradientAt_iff f y g).1 hg x)

/-- Helper for Chapter14 Exercise 14.6: the support family based at `x` contains the touching
value `f x`. -/
lemma le_sSup_subgradientAffineSupportValueSet_self
    (f : Point → ℝ) (h_convex : ConvexOn ℝ Set.univ f) (x : Point) :
    f x ≤ sSup (subgradientAffineSupportValueSet f x x) := by
  rcases exists_subgradientAt_of_convexOn f h_convex x with ⟨g, hg⟩
  have hx_mem : f x ∈ subgradientAffineSupportValueSet f x x := by
    -- The supporting affine minorant based at `x` touches the graph at `x` itself.
    refine (mem_subgradientAffineSupportValueSet_iff f x x (f x)).2 ?_
    refine ⟨g, hg, ?_⟩
    simp
  have h_bdd : BddAbove (subgradientAffineSupportValueSet f x x) := by
    refine ⟨f x, ?_⟩
    intro r hr
    rcases (mem_subgradientAffineSupportValueSet_iff f x x r).1 hr with ⟨g, hg, hgr⟩
    rw [← hgr]
    simp
  exact le_csSup h_bdd hx_mem

/-- Chapter14 Exercise 14.6: if `f` is convex on `ℝ^n`, then at every `x` its value equals the
double supremum of the supporting-affine values `f y + ⟪g, x - y⟫` over all base points `y` and
all subgradients `g ∈ ∂ f(y)`. -/
theorem convexOn_eq_sSup_subgradientAffineSupportValue
    (f : Point → ℝ)
    (h_convex : ConvexOn ℝ Set.univ f)
    (x : Point) :
    f x =
      sSup (Set.range fun y : Point ↦
        sSup (subgradientAffineSupportValueSet f x y)) := by
  let outerSet : Set ℝ := Set.range fun y : Point ↦ sSup (subgradientAffineSupportValueSet f x y)
  apply le_antisymm
  · -- The support family based at `x` already attains the touching value `f x`.
    have h_outer_bdd : BddAbove outerSet := by
      refine ⟨f x, ?_⟩
      intro r hr
      rcases hr with ⟨y, rfl⟩
      exact sSup_subgradientAffineSupportValueSet_le f h_convex x y
    have hx_inner : f x ≤ sSup (subgradientAffineSupportValueSet f x x) :=
      le_sSup_subgradientAffineSupportValueSet_self f h_convex x
    have hx_outer : sSup (subgradientAffineSupportValueSet f x x) ≤ sSup outerSet := by
      exact le_csSup h_outer_bdd (Set.mem_range_self x)
    exact hx_inner.trans hx_outer
  · -- Every inner support supremum is bounded above by `f x`, so the outer supremum is too.
    have h_outer_nonempty : outerSet.Nonempty := ⟨_, Set.mem_range_self x⟩
    exact csSup_le h_outer_nonempty (by
      intro r hr
      rcases hr with ⟨y, rfl⟩
      exact sSup_subgradientAffineSupportValueSet_le f h_convex x y)

#print axioms subgradientAffineSupportValueSet

end
