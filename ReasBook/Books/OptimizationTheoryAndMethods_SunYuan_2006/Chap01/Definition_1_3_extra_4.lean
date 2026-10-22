/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import ConvexAnalysisMonotoneOperators_BauschkeCombettes_2017.Chap06.Proposition_6_33
import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Calculus.TangentCone.Seq
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Topology.Sequences

-- Domain sampling:
-- * primary domain: one-sided tangent cones in real normed spaces, with the source-facing normal
--   cone recovered from an inner-product inequality
-- * inspected canonical owners:
--   `posTangentConeAt`
--   `tangentConeAt_closure`
--   `mem_tangentConeAt_iff_exists_seq`
--   `sub_mem_posTangentConeAt_of_segment_subset`
-- * source/core/bridge triage:
--   `source-facing`: the normal cone `normalConeAt S xbar` and the book's tangent-cone
--     description at `xbar`
--   `core/canonical`: the positive tangent cone `posTangentConeAt S xbar`
--   `bridge/view`: the set-level polarity, closure, and sequential characterizations of
--     `posTangentConeAt S xbar`
-- * primitive data vs derived API:
--   `normalConeAt S xbar` is primitive set-valued data, while the tangent/normal polarity and
--   closure/sequence descriptions stay as derived bridge theorems

open scoped RealInnerProductSpace

universe u

section Chapter01Definition13Extra4

open Filter

/-- Helper for Chapter01 Definition 1.3-extra-4: the set of nonnegative scaled feasible
displacements `a • (x - xbar)` from `xbar`. -/
def nonnegScaledSub
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    (S : Set E) (xbar : E) : Set E :=
  { d | ∃ a : ℝ, 0 ≤ a ∧ ∃ x ∈ S, d = a • (x - xbar) }

/-- Helper for Chapter01 Definition 1.3-extra-4: `0` is one of the scaled feasible displacements
as soon as the witness point lies in `S`. -/
theorem zero_mem_nonnegScaledSub
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {xbar : E} (hxbar : xbar ∈ S) :
    0 ∈ nonnegScaledSub S xbar := by
  -- Use the zero scalar at the base point.
  refine ⟨0, le_rfl, xbar, hxbar, ?_⟩
  simp

/-- Helper for Chapter01 Definition 1.3-extra-4: the generator set is stable under
nonnegative real scaling. -/
theorem smul_mem_nonnegScaledSub
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {xbar d : E} (hd : d ∈ nonnegScaledSub S xbar) {a : ℝ} (ha : 0 ≤ a) :
    a • d ∈ nonnegScaledSub S xbar := by
  -- Multiply the generator scalar and keep the same feasible point.
  rcases hd with ⟨b, hb, x, hx, rfl⟩
  refine ⟨a * b, mul_nonneg ha hb, x, hx, ?_⟩
  rw [smul_smul]

/-- Helper for Chapter01 Definition 1.3-extra-4: the generator set is closed under addition for a
convex feasible set. -/
theorem add_mem_nonnegScaledSub
    {E : Type u} [AddCommGroup E] [Module ℝ E]
    {S : Set E} {xbar d₁ d₂ : E} (hS_convex : Convex ℝ S)
    (hd₁ : d₁ ∈ nonnegScaledSub S xbar) (hd₂ : d₂ ∈ nonnegScaledSub S xbar) :
    d₁ + d₂ ∈ nonnegScaledSub S xbar := by
  rcases hd₁ with ⟨a₁, ha₁, x₁, hx₁, rfl⟩
  rcases hd₂ with ⟨a₂, ha₂, x₂, hx₂, rfl⟩
  by_cases hsum : a₁ + a₂ = 0
  · -- If the total weight vanishes, both summands are already zero.
    have ha₁_zero : a₁ = 0 := by linarith
    have ha₂_zero : a₂ = 0 := by linarith
    subst ha₁_zero
    subst ha₂_zero
    refine ⟨0, le_rfl, x₁, hx₁, ?_⟩
    simp
  · -- Otherwise, repackage the sum through the convex combination of the two feasible points.
    have hsum_pos : 0 < a₁ + a₂ := by
      exact lt_of_le_of_ne (add_nonneg ha₁ ha₂) (Ne.symm hsum)
    let t : ℝ := a₂ / (a₁ + a₂)
    have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨div_nonneg ha₂ (le_of_lt hsum_pos), ?_⟩
      rw [div_le_iff₀ hsum_pos]
      linarith
    let x : E := x₁ + t • (x₂ - x₁)
    have hx : x ∈ S := by
      exact hS_convex.add_smul_sub_mem hx₁ hx₂ ht
    have hmul : (a₁ + a₂) * t = a₂ := by
      dsimp [t]
      field_simp [hsum]
    refine ⟨a₁ + a₂, add_nonneg ha₁ ha₂, x, hx, ?_⟩
    dsimp [x, t]
    calc
      a₁ • (x₁ - xbar) + a₂ • (x₂ - xbar)
          = a₁ • (x₁ - xbar) + (a₂ • (x₁ - xbar) + a₂ • (x₂ - x₁)) := by
              have hdecomp : x₂ - xbar = (x₁ - xbar) + (x₂ - x₁) := by
                abel
              rw [hdecomp, smul_add]
      _ = (a₁ + a₂) • (x₁ - xbar) + a₂ • (x₂ - x₁) := by
            rw [add_smul]
            abel
      _ = (a₁ + a₂) • (x₁ - xbar) + (a₁ + a₂) • (t • (x₂ - x₁)) := by
            rw [smul_smul, hmul]
      _ = (a₁ + a₂) • ((x₁ - xbar) + t • (x₂ - x₁)) := by
            rw [smul_add]
      _ = (a₁ + a₂) • ((x₁ + t • (x₂ - x₁)) - xbar) := by
            congr 1
            simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (a₁ + a₂) • (x - xbar) := by
            rfl

/-- The normal cone of `S` at `xbar` is the set of vectors whose inner product with every
feasible displacement `x - xbar` is nonpositive. -/
def normalConeAt
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (S : Set E) (xbar : E) : Set E :=
  { y | ∀ x ∈ S, ⟪y, x - xbar⟫ ≤ (0 : ℝ) }

/-- Membership in `normalConeAt S xbar` is the defining pointwise inequality. -/
theorem mem_normalConeAt_iff
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {xbar y : E} :
    y ∈ normalConeAt S xbar ↔ ∀ x ∈ S, ⟪y, x - xbar⟫ ≤ (0 : ℝ) := by
  exact Iff.rfl

/-- Closing the underlying set does not change the normal cone. -/
theorem normalConeAt_closure
    {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {S : Set E} {xbar : E} :
    normalConeAt (closure S) xbar = normalConeAt S xbar := by
  ext y
  constructor
  · intro hy
    exact fun x hx ↦ hy x (subset_closure hx)
  · intro hy x hx
    have hsub : S ⊆ {z : E | ⟪y, z - xbar⟫ ≤ (0 : ℝ)} := by
      intro z hz
      exact hy z hz
    have hclosed : IsClosed {z : E | ⟪y, z - xbar⟫ ≤ (0 : ℝ)} := by
      exact isClosed_le
        (continuous_const.inner (continuous_id.sub continuous_const))
        continuous_const
    exact closure_minimal hsub hclosed hx

/-- Helper for Chapter01 Definition 1.3-extra-4: the positive tangent cone is stable under
nonnegative real scaling. -/
theorem smul_mem_posTangentConeAt
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {xbar d : E} (hd : d ∈ posTangentConeAt S xbar) {a : ℝ} (ha : 0 ≤ a) :
    a • d ∈ posTangentConeAt S xbar := by
  -- Reuse the same tangent-cone sequence and absorb the new scale into the scalar sequence.
  rw [mem_tangentConeAt_iff_exists_seq] at hd ⊢
  rcases hd with ⟨c, δ, hδ, hS, hcd⟩
  let aNN : NNReal := ⟨a, ha⟩
  let c' : ℕ → NNReal := fun n ↦ c n * aNN
  refine ⟨c', δ, hδ, hS, ?_⟩
  have hscaled :
      Tendsto (fun n ↦ a • ((c n : ℝ) • δ n)) atTop (nhds (a • d)) :=
    (continuous_const_smul a).tendsto d |>.comp (by simpa [NNReal.smul_def] using hcd)
  have hfun :
      (fun n ↦ c' n • δ n) = fun n ↦ a • ((c n : ℝ) • δ n) := by
    funext n
    dsimp [c', aNN]
    rw [NNReal.smul_def, smul_smul]
    have hmul : ((c n * aNN : NNReal) : ℝ) = a * (c n : ℝ) := by
      change (c n : ℝ) * (aNN : ℝ) = a * (c n : ℝ)
      rw [show ((aNN : NNReal) : ℝ) = a by rfl, mul_comm]
    rw [hmul]
  rw [hfun]
  exact hscaled

/-- Helper for Chapter01 Definition 1.3-extra-4: tangent directions can be written as limits of
nonnegative scaled feasible displacements. -/
theorem mem_posTangentConeAt_iff_exists_seq_nonneg_smul_sub_aux
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {xbar d : E} (hxbar : xbar ∈ S) :
    d ∈ posTangentConeAt S xbar ↔
      ∃ c : ℕ → ℝ, ∃ x : ℕ → E,
        Tendsto x atTop (nhds xbar) ∧
        (∀ n, 0 ≤ c n) ∧
        (∀ n, x n ∈ S) ∧
        Tendsto (fun n ↦ c n • (x n - xbar)) atTop (nhds d) := by
  constructor
  · intro hd
    classical
    -- Start from mathlib's tangent-cone sequence and repair the finitely many bad indices.
    rw [mem_tangentConeAt_iff_exists_seq] at hd
    rcases hd with ⟨c, δ, hδ, hS, hcd⟩
    let x : ℕ → E := fun n ↦ if h : xbar + δ n ∈ S then xbar + δ n else xbar
    let cReal : ℕ → ℝ := fun n ↦ c n
    have hx_eventually : (fun n ↦ x n) =ᶠ[atTop] fun n ↦ xbar + δ n := by
      filter_upwards [hS] with n hn
      simp [x, hn]
    have hx_tendsto : Tendsto x atTop (nhds xbar) := by
      have hsum : Tendsto (fun n ↦ xbar + δ n) atTop (nhds xbar) := by
        simpa [add_zero] using tendsto_const_nhds.add hδ
      exact Tendsto.congr' hx_eventually.symm hsum
    have hx_mem : ∀ n, x n ∈ S := by
      intro n
      by_cases h : xbar + δ n ∈ S
      · simp [x, h]
      · simp [x, h, hxbar]
    have hsmul_eventually :
        (fun n ↦ cReal n • (x n - xbar)) =ᶠ[atTop] fun n ↦ (c n : ℝ) • δ n := by
      filter_upwards [hx_eventually] with n hn
      simp [cReal, hn]
    have hlimit : Tendsto (fun n ↦ cReal n • (x n - xbar)) atTop (nhds d) := by
      exact Tendsto.congr' hsmul_eventually.symm (by simpa [cReal, NNReal.smul_def] using hcd)
    exact ⟨cReal, x, hx_tendsto, fun n ↦ (c n).2, hx_mem, hlimit⟩
  · rintro ⟨c, x, hx_tendsto, hc, hx_mem, hlimit⟩
    -- Turn the repaired textbook-style sequence back into the canonical tangent-cone sequence.
    let cNN : ℕ → NNReal := fun n ↦ ⟨c n, hc n⟩
    have hsub : Tendsto (fun n ↦ x n - xbar) atTop (nhds 0) := by
      have hconst : Tendsto (fun _ : ℕ ↦ xbar) atTop (nhds xbar) := tendsto_const_nhds
      simpa using hx_tendsto.sub hconst
    have hmem : ∀ᶠ n in atTop, xbar + (x n - xbar) ∈ S := by
      exact .of_forall (fun n ↦ by simpa using hx_mem n)
    have hlimit' : Tendsto (fun n ↦ cNN n • (x n - xbar)) atTop (nhds d) := by
      change Tendsto (fun n ↦ ((cNN n : NNReal) : ℝ) • (x n - xbar)) atTop (nhds d)
      have hcNN :
          (fun n ↦ ((cNN n : NNReal) : ℝ) • (x n - xbar)) =
            fun n ↦ c n • (x n - xbar) := by
        funext n
        change c n • (x n - xbar) = c n • (x n - xbar)
        rfl
      rw [hcNN]
      exact hlimit
    exact mem_tangentConeAt_of_seq atTop cNN (fun n ↦ x n - xbar) hsub hmem hlimit'

/-- Helper for Chapter01 Definition 1.3-extra-4: the positive tangent cone is the closure of the
nonnegative scaled feasible displacements. -/
theorem posTangentConeAt_eq_closure_nonneg_smul_sub_aux
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {xbar : E} (hS_convex : Convex ℝ S) (hxbar : xbar ∈ S) :
    posTangentConeAt S xbar = closure (nonnegScaledSub S xbar) := by
  ext d
  constructor
  · intro hd
    -- Use the sequence description to exhibit `d` as a sequential closure point of the generators.
    rw [mem_closure_iff_seq_limit]
    rcases (mem_posTangentConeAt_iff_exists_seq_nonneg_smul_sub_aux (S := S) (xbar := xbar)
        (d := d) hxbar).1 hd with ⟨c, x, -, hc, hx, hlimit⟩
    refine ⟨fun n ↦ c n • (x n - xbar), ?_, hlimit⟩
    intro n
    exact ⟨c n, hc n, x n, hx n, rfl⟩
  · intro hd
    -- First put every generator into the tangent cone, then use closedness of the tangent cone.
    refine closure_minimal ?_ ?_ hd
    · intro d hd'
      rcases hd' with ⟨a, ha, x, hx, rfl⟩
      have hbase : x - xbar ∈ posTangentConeAt S xbar := by
        exact sub_mem_posTangentConeAt_of_segment_subset (hS_convex.segment_subset hxbar hx)
      exact smul_mem_posTangentConeAt hbase ha
    · simpa [posTangentConeAt, tangentConeAt_eq_biInter_closure] using
        (isClosed_iInter fun U ↦ isClosed_iInter fun _ ↦ isClosed_closure)

section

variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Chapter01 Definition 1.3-extra-4: in a finite-dimensional real inner-product space, if `S` is
a closed convex set and `xbar ∈ S`, then the book's tangent cone at `xbar` is represented by the
canonical positive tangent cone `posTangentConeAt S xbar`, and it is exactly the set-level polar
of `normalConeAt S xbar`. -/
theorem posTangentConeAt_eq_polar_normalConeAt {S : Set E} {xbar : E}
    (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) (hxbar : xbar ∈ S) :
    posTangentConeAt S xbar =
      { d | ∀ y ∈ normalConeAt S xbar, ⟪d, y⟫ ≤ (0 : ℝ) } := by
  -- Build the canonical closed cone generated by the feasible displacements.
  let K : ConvexCone ℝ E := {
    carrier := nonnegScaledSub S xbar
    smul_mem' := fun a ha d hd ↦ smul_mem_nonnegScaledSub (S := S) (xbar := xbar) hd ha.le
    add_mem' := fun d₁ hd₁ d₂ hd₂ ↦
      add_mem_nonnegScaledSub (S := S) (xbar := xbar) hS_convex hd₁ hd₂
  }
  let C0 : ConvexCone ℝ E := K.closure
  have hC0 : (C0 : Set E).Nonempty ∧ IsClosed (C0 : Set E) := by
    refine ⟨?_, ?_⟩
    · rw [ConvexCone.coe_closure]
      exact ⟨0, subset_closure (zero_mem_nonnegScaledSub (S := S) (xbar := xbar) hxbar)⟩
    · rw [ConvexCone.coe_closure]
      exact isClosed_closure
  obtain ⟨C, hCeq⟩ := CanLift.prf (β := ProperCone ℝ E) C0 hC0
  have hCset : (C : Set E) = closure (nonnegScaledSub S xbar) := by
    have hCeqSet : ((C : ConvexCone ℝ E) : Set E) = (C0 : Set E) := by
      exact congrArg (fun D : ConvexCone ℝ E => (D : Set E)) hCeq
    have hC0set : (C0 : Set E) = closure (nonnegScaledSub S xbar) := by
      simpa [C0, K] using (ConvexCone.coe_closure K)
    rw [hC0set] at hCeqSet
    exact hCeqSet
  have hpos :
      posTangentConeAt S xbar = (C : Set E) := by
    -- Reuse the earlier closure characterization of the positive tangent cone.
    rw [hCset]
    simpa using
      posTangentConeAt_eq_closure_nonneg_smul_sub_aux (S := S) (xbar := xbar) hS_convex hxbar
  have hnormal :
      normalConeAt S xbar = { y | -y ∈ ProperCone.innerDual (C : Set E) } := by
    ext y
    constructor
    · intro hy
      -- Extend the defining normal-cone inequalities from generators to the closed generator cone.
      change -y ∈ ProperCone.innerDual (C : Set E)
      rw [ProperCone.mem_innerDual]
      intro d hd
      have hsubset : nonnegScaledSub S xbar ⊆ { z : E | 0 ≤ ⟪z, -y⟫ } := by
        intro z hz
        rcases hz with ⟨a, ha, x, hx, rfl⟩
        have hyx : ⟪y, x - xbar⟫ ≤ (0 : ℝ) := hy x hx
        have hyx' : 0 ≤ ⟪x - xbar, -y⟫ := by
          have : 0 ≤ -⟪y, x - xbar⟫ := neg_nonneg.mpr hyx
          simpa [real_inner_comm] using this
        have hscaled : 0 ≤ a * ⟪x - xbar, -y⟫ := mul_nonneg ha hyx'
        simpa [real_inner_smul_left] using hscaled
      rw [hCset] at hd
      exact closure_minimal hsubset
        (isClosed_le continuous_const (continuous_id.inner continuous_const)) hd
    · intro hy
      -- Evaluate the inner-dual inequality on the basic generators `x - xbar`.
      rw [mem_normalConeAt_iff]
      intro x hx
      have hxgen : x - xbar ∈ (C : Set E) := by
        rw [hCset]
        exact subset_closure ⟨1, zero_le_one, x, hx, by simp⟩
      have hinner : 0 ≤ ⟪x - xbar, -y⟫ := by
        exact (ProperCone.mem_innerDual.mp hy) hxgen
      have : 0 ≤ -⟪y, x - xbar⟫ := by
        simpa [real_inner_comm] using hinner
      exact neg_nonneg.mp this
  ext d
  constructor
  · intro hd
    -- A tangent direction pairs nonpositively with every normal vector.
    rw [Set.mem_setOf_eq]
    intro y hy
    have hy' : -y ∈ ProperCone.innerDual (C : Set E) := by
      simpa [hnormal] using hy
    have hd' : d ∈ (C : Set E) := by
      simpa [hpos] using hd
    have hinner : 0 ≤ ⟪d, -y⟫ := (ProperCone.mem_innerDual.mp hy') hd'
    exact neg_nonneg.mp (by simpa using hinner)
  · intro hd
    -- The polar description is the double inner dual of the closed generator cone.
    have hd' : d ∈ ProperCone.innerDual (ProperCone.innerDual (C : Set E) : Set E) := by
      rw [ProperCone.mem_innerDual]
      intro y hy
      have hy' : -y ∈ normalConeAt S xbar := by
        simpa [hnormal] using hy
      have hineq : ⟪d, -y⟫ ≤ (0 : ℝ) := hd (-y) hy'
      exact neg_nonpos.mp (by simpa [real_inner_comm] using hineq)
    have hd'' : d ∈ (C : Set E) := by
      simpa using hd'
    simpa [hpos] using hd''

/-- Helper for Chapter01 Definition 1.3-extra-4: membership in the tangent cone of a closed convex
set is tested by the defining inequalities against the normal cone. -/
theorem mem_posTangentConeAt_iff_nonpos_inner_normalConeAt {S : Set E} {xbar d : E}
    (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) (hxbar : xbar ∈ S) :
    d ∈ posTangentConeAt S xbar ↔
      ∀ y ∈ normalConeAt S xbar, ⟪d, y⟫ ≤ (0 : ℝ) := by
  -- Read the set equality pointwise.
  rw [posTangentConeAt_eq_polar_normalConeAt hS_closed hS_convex hxbar]
  rfl

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Chapter01 Definition 1.3-extra-4: if `S` is a closed convex set and `xbar ∈ S`,
then the tangent cone of `S` at `xbar`, expressed by `posTangentConeAt S xbar`, is the closure of
the nonnegative scaled differences `λ • (x - xbar)` with `λ ≥ 0` and `x ∈ S`. -/
theorem posTangentConeAt_eq_closure_nonneg_smul_sub {S : Set E} {xbar : E}
    (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) (hxbar : xbar ∈ S) :
    posTangentConeAt S xbar =
      closure
        { d : E |
            ∃ a : ℝ, 0 ≤ a ∧ ∃ x ∈ S, d = a • (x - xbar) } := by
  -- Reuse the earlier auxiliary closure description.
  simpa [nonnegScaledSub] using
    posTangentConeAt_eq_closure_nonneg_smul_sub_aux (S := S) (xbar := xbar) hS_convex hxbar

end

section

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Helper for Chapter01 Definition 1.3-extra-4: if `S` is a closed convex set and `xbar ∈ S`,
then a vector `d` lies in the tangent cone of `S` at `xbar`, expressed by
`posTangentConeAt S xbar`, exactly when it can be
realized as the limit of nonnegative scaled differences `c n • (x n - xbar)` with `x n ∈ S`
and `x n ⟶ xbar`. -/
theorem mem_posTangentConeAt_iff_exists_seq_nonneg_smul_sub {S : Set E} {xbar d : E}
    (hS_closed : IsClosed S) (hS_convex : Convex ℝ S) (hxbar : xbar ∈ S) :
    d ∈ posTangentConeAt S xbar ↔
      ∃ c : ℕ → ℝ, ∃ x : ℕ → E,
        Tendsto x atTop (nhds xbar) ∧
        (∀ n, 0 ≤ c n) ∧
        (∀ n, x n ∈ S) ∧
        Tendsto (fun n ↦ c n • (x n - xbar)) atTop (nhds d) := by
  -- Reuse the earlier auxiliary sequence description.
  simpa using
    mem_posTangentConeAt_iff_exists_seq_nonneg_smul_sub_aux (S := S) (xbar := xbar)
      (d := d) hxbar

end

end Chapter01Definition13Extra4
