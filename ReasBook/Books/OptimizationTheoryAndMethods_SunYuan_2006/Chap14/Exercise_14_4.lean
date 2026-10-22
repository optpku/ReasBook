/-
Authors: Chenyi Li, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/OptimizationTheoryAndMethods_SunYuan_2006/README.md (Contributors).
-/

import OptimizationTheoryAndMethods_SunYuan_2006.Compat
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WeakDual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Data.Real.Basic
import OptimizationTheoryAndMethods_SunYuan_2006.Chap14.Exercise_14_3

noncomputable section

open InnerProductSpace
open scoped BigOperators
open scoped ClarkeDirectionalDerivative ClarkeDifferential

section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

local notation "DualPoint" => StrongDual ℝ E
local notation "WeakDualPoint" => WeakDual ℝ E

/-
Domain sampling:
- primary domain: Clarke differentials of finite maxima and finite sums of smooth scalar fields
- sampled owner declarations: `clarkeDifferential`,
  `clarkeDifferential_eq_of_locallyLipschitzAt`
- sampled bridge/view declarations: `ContDiffAt.locallyLipschitzAt`,
  `clarkeDifferentialOfLocallyLipschitzAt`
- core/canonical owner: `clarkeDifferential`
- primitive source-facing data in this exercise: the active index set and admissible sign families
- derived API refined here: Clarke-differential bridges for finite pointwise maxima and absolute
  sums at a point
- finite-operational owners: `Finset.sup'`, `Finset.sum`, and `convexHull`
-/

/-- The active index set for the finite-family maximum over `s` at `x`: those indices in `s`
whose value equals the maximum of `c · x` on `s`. -/
def activeIndices {ι : Type*} (s : Finset ι) (c : ι → E → ℝ) (x : E) : Set ι :=
  {i | i ∈ s ∧ ∀ j ∈ s, c j x ≤ c i x}

/-- The admissible coefficient families, indexed intrinsically by the finite owner `s`, for the
Clarke differential of the finite sum `y ↦ ∑ i in s, |c i y|` at `x`. -/
def absoluteSumCoefficients {ι : Type*} (s : Finset ι) (c : ι → E → ℝ) (x : E) :
    Set (↑s → ℝ) :=
  {μ |
    (∀ i : ↑s, 0 < c i x → μ i = 1) ∧
    (∀ i : ↑s, c i x < 0 → μ i = -1) ∧
    ∀ i : ↑s, c i x = 0 → μ i ∈ Set.Icc (-1 : ℝ) 1}

/-- Helper for Chapter14 Exercise 14.4: under the local Lipschitz hypothesis needed for the
textbook Clarke calculus, the Clarke differential is convex. -/
theorem convex_clarkeDifferential_local_of_locallyLipschitzAt
    (f : E → ℝ) (x : E) (h_local : LocallyLipschitzAt f x) :
    Convex ℝ (clarkeDifferential f x) := by
  -- Move the defining inequalities to the real-valued Clarke owner and then combine them
  -- linearly using the convex-combination coefficients.
  intro ξ hξ η hη a b ha hb hab d
  have hξdE : ((ξ d : ℝ) : EReal) ≤ ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) := by
    simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local] using
      ((mem_clarkeDifferential_iff f x ξ).mp hξ d)
  have hηdE : ((η d : ℝ) : EReal) ≤ ((clarkeDirectionalDerivReal f x d : ℝ) : EReal) := by
    simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local] using
      ((mem_clarkeDifferential_iff f x η).mp hη d)
  have hξd : ξ d ≤ clarkeDirectionalDerivReal f x d := by
    exact_mod_cast hξdE
  have hηd : η d ≤ clarkeDirectionalDerivReal f x d := by
    exact_mod_cast hηdE
  have hcomb : a * ξ d + b * η d ≤ clarkeDirectionalDerivReal f x d := by
    calc
    a * ξ d + b * η d
        ≤ a * clarkeDirectionalDerivReal f x d + b * clarkeDirectionalDerivReal f x d := by
            gcongr
    _ = (a + b) * clarkeDirectionalDerivReal f x d := by ring
    _ = clarkeDirectionalDerivReal f x d := by simp [hab]
  have hcombE :
      (((a * ξ d + b * η d : ℝ) : EReal) ≤ clarkeDirectionalDeriv f x d) := by
    have hcombE' :
        (((a * ξ d + b * η d : ℝ) : EReal) ≤
          ((clarkeDirectionalDerivReal f x d : ℝ) : EReal)) := by
      exact_mod_cast hcomb
    simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d h_local] using hcombE'
  simpa [smul_eq_mul, add_comm, add_left_comm, add_assoc] using hcombE

/-- Helper for Chapter14 Exercise 14.4: a weak-* closed convex subset of `WeakDual ℝ E` is
exactly the intersection of the evaluation halfspaces that contain it. -/
lemma mem_closed_convex_iff_eval_halfspaces
    {S : Set WeakDualPoint} {ξ : WeakDualPoint}
    (h_conv : Convex ℝ S) (h_closed : IsClosed S) :
    ξ ∈ S ↔ ∀ d : E, ∃ η ∈ S, ξ d ≤ η d := by
  constructor
  · intro hξ d
    -- Membership is witnessed by the same point of the closed convex set.
    exact ⟨ξ, hξ, le_rfl⟩
  · intro h_eval
    letI : LocallyConvexSpace ℝ WeakDualPoint :=
      WeakBilin.locallyConvexSpace (B := topDualPairing ℝ E)
    -- Every continuous linear functional on the weak dual is evaluation at some vector `d`.
    rw [← iInter_halfSpaces_eq h_conv h_closed]
    rw [Set.mem_iInter]
    intro l
    obtain ⟨d, rfl⟩ :=
      LinearMap.dualEmbedding_surjective (topDualPairing ℝ E) l
    obtain ⟨η, hηS, hle⟩ := h_eval d
    refine ⟨η, hηS, ?_⟩
    change ξ d ≤ η d
    exact hle

/-- Helper for Chapter14 Exercise 14.4: the active index set is nonempty because a finite
maximum is attained on the owner `s`. -/
theorem activeIndices_nonempty {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (c : ι → E → ℝ)
    (x : E) :
    (activeIndices s c x).Nonempty := by
  classical
  rcases Finset.exists_mem_eq_sup' hs (fun i ↦ c i x) with ⟨i, his, hiMax⟩
  refine ⟨i, ?_⟩
  refine ⟨his, ?_⟩
  intro j hjs
  have hjle : c j x ≤ s.sup' hs (fun k ↦ c k x) :=
    Finset.le_sup'_of_le (s := s) (f := fun k ↦ c k x) hjs le_rfl
  simpa [hiMax] using hjle

/-- Helper for Chapter14 Exercise 14.4: the active-gradient set is finite because the active
indices form a subset of the finite owner `s`. -/
theorem finite_activeGradients {ι : Type*} [CompleteSpace E]
    (s : Finset ι) (c : ι → E → ℝ) (x : E) :
    (((fun i ↦ toDual ℝ E (gradient (c i) x)) '' activeIndices s c x) : Set DualPoint).Finite := by
  classical
  have hsubset : activeIndices s c x ⊆ (↑s : Set ι) := by
    intro i hi
    exact hi.1
  exact (s.finite_toSet.subset hsubset).image (fun i ↦ toDual ℝ E (gradient (c i) x))

/-- Helper for Chapter14 Exercise 14.4: the admissible coefficient box is nonempty; choose the
canonical sign coefficient `1`, `-1`, or `0` according to the sign of `c_i(x)`. -/
theorem absoluteSumCoefficients_nonempty {ι : Type*} (s : Finset ι) (c : ι → E → ℝ) (x : E) :
    (absoluteSumCoefficients s c x).Nonempty := by
  classical
  let μ : ↑s → ℝ := fun i ↦
    if 0 < c i x then 1 else if c i x < 0 then -1 else 0
  refine ⟨μ, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i hi_pos
    simp [μ, hi_pos, not_lt.mpr hi_pos.le]
  · intro i hi_neg
    have hnot_pos : ¬ 0 < c i x := not_lt.mpr hi_neg.le
    simp [μ, hnot_pos, hi_neg]
  · intro i hi_zero
    have hnot_pos : ¬ 0 < c i x := by simpa [hi_zero]
    have hnot_neg : ¬ c i x < 0 := by simpa [hi_zero]
    simp [μ, hnot_pos, hnot_neg, hi_zero]

/-- Helper for Chapter14 Exercise 14.4: the absolute-sum target set is nonempty because the
coefficient box already contains a canonical sign choice. -/
theorem absoluteSum_target_nonempty {ι : Type*} [CompleteSpace E]
    (s : Finset ι) (c : ι → E → ℝ) (x : E) :
    ((fun μ : ↑s → ℝ ↦
        Finset.sum s.attach (fun i ↦ μ i • toDual ℝ E (gradient (c i) x))) ''
      absoluteSumCoefficients s c x).Nonempty := by
  rcases absoluteSumCoefficients_nonempty (E := E) s c x with ⟨μ, hμ⟩
  exact ⟨_, ⟨μ, hμ, rfl⟩⟩

/-- Helper for Chapter14 Exercise 14.4: the pointwise maximum of two scalar fields that are
locally Lipschitz at `x` is locally Lipschitz at `x`. -/
theorem locallyLipschitzAt_max_of_locallyLipschitzAt {f g : E → ℝ} {x : E}
    (hf : LocallyLipschitzAt f x) (hg : LocallyLipschitzAt g x) :
    LocallyLipschitzAt (fun y ↦ Max.max (f y) (g y)) x := by
  rcases locallyLipschitzAt_iff.mp hf with ⟨εf, hεf, Kf, hKf⟩
  rcases locallyLipschitzAt_iff.mp hg with ⟨εg, hεg, Kg, hKg⟩
  refine locallyLipschitzAt_iff.mpr ?_
  refine ⟨min εf εg, lt_min hεf hεg, Max.max Kf Kg, ?_⟩
  -- Work on the smaller closed ball where both original Lipschitz bounds are available.
  refine LipschitzOnWith.of_dist_le_mul
    (s := Metric.closedBall x (min εf εg))
    (f := fun y ↦ Max.max (f y) (g y))
    (K := Max.max Kf Kg) fun y hy z hz ↦ ?_
  have hyf : y ∈ Metric.closedBall x εf :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hy
  have hzf : z ∈ Metric.closedBall x εf :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hz
  have hyg : y ∈ Metric.closedBall x εg :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hy
  have hzg : z ∈ Metric.closedBall x εg :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hz
  -- The real-valued maximum is 1-Lipschitz in its two scalar inputs.
  calc
    dist (Max.max (f y) (g y)) (Max.max (f z) (g z))
        = |Max.max (f y) (g y) - Max.max (f z) (g z)| := by
            rw [Real.dist_eq]
    _ ≤ Max.max |f y - f z| |g y - g z| := abs_max_sub_max_le_max _ _ _ _
    _ = Max.max (dist (f y) (f z)) (dist (g y) (g z)) := by
          rw [Real.dist_eq, Real.dist_eq]
    _ ≤ Max.max Kf Kg * dist y z := by
          refine max_le_iff.mpr ⟨?_, ?_⟩
          · exact (hKf.dist_le_mul y hyf z hzf).trans <|
              mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
          · exact (hKg.dist_le_mul y hyg z hzg).trans <|
              mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg

/-- Helper for Chapter14 Exercise 14.4: composing a locally Lipschitz scalar field with the
absolute value preserves local Lipschitz continuity at `x`. -/
theorem locallyLipschitzAt_abs_of_locallyLipschitzAt {f : E → ℝ} {x : E}
    (hf : LocallyLipschitzAt f x) :
    LocallyLipschitzAt (fun y ↦ |f y|) x := by
  rcases locallyLipschitzAt_iff.mp hf with ⟨ε, hε, K, hK⟩
  refine locallyLipschitzAt_iff.mpr ?_
  refine ⟨ε, hε, K, ?_⟩
  -- The scalar absolute value is globally 1-Lipschitz, so the closed-ball constant is unchanged.
  refine LipschitzOnWith.of_dist_le_mul
    (s := Metric.closedBall x ε)
    (f := fun y ↦ |f y|)
    (K := K) fun y hy z hz ↦ ?_
  calc
    dist |f y| |f z| = |(|f y| - |f z|)| := by rw [Real.dist_eq]
    _ ≤ |f y - f z| := abs_abs_sub_abs_le_abs_sub _ _
    _ = dist (f y) (f z) := by rw [Real.dist_eq]
    _ ≤ K * dist y z := hK.dist_le_mul y hy z hz

/-- Helper for Chapter14 Exercise 14.4: the sum of two locally Lipschitz scalar fields is locally
Lipschitz at `x`. -/
theorem locallyLipschitzAt_add_real_of_locallyLipschitzAt {f g : E → ℝ} {x : E}
    (hf : LocallyLipschitzAt f x) (hg : LocallyLipschitzAt g x) :
    LocallyLipschitzAt (fun y ↦ f y + g y) x := by
  rcases locallyLipschitzAt_iff.mp hf with ⟨εf, hεf, Kf, hKf⟩
  rcases locallyLipschitzAt_iff.mp hg with ⟨εg, hεg, Kg, hKg⟩
  refine locallyLipschitzAt_iff.mpr ?_
  refine ⟨min εf εg, lt_min hεf hεg, Kf + Kg, ?_⟩
  -- Intersect the two closed-ball witnesses and add the branchwise distance estimates.
  refine LipschitzOnWith.of_dist_le_mul
    (s := Metric.closedBall x (min εf εg))
    (f := fun y ↦ f y + g y)
    (K := Kf + Kg) fun y hy z hz ↦ ?_
  have hyf : y ∈ Metric.closedBall x εf :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hy
  have hzf : z ∈ Metric.closedBall x εf :=
    Metric.closedBall_subset_closedBall (min_le_left _ _) hz
  have hyg : y ∈ Metric.closedBall x εg :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hy
  have hzg : z ∈ Metric.closedBall x εg :=
    Metric.closedBall_subset_closedBall (min_le_right _ _) hz
  calc
    dist (f y + g y) (f z + g z)
        ≤ dist (f y) (f z) + dist (g y) (g z) := by
            simpa [dist_eq_norm, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using
              dist_add_add_le (f y) (g y) (f z) (g z)
    _ ≤ Kf * dist y z + Kg * dist y z := add_le_add
          (hKf.dist_le_mul y hyf z hzf) (hKg.dist_le_mul y hyg z hzg)
    _ = (Kf + Kg) * dist y z := by ring

/-- Helper for Chapter14 Exercise 14.4: a finite sum of locally Lipschitz scalar fields is
locally Lipschitz at `x`. -/
theorem locallyLipschitzAt_finsetSum_of_locallyLipschitzAt
    {ι : Type*}
    (s : Finset ι)
    (f : ι → E → ℝ)
    (x : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    LocallyLipschitzAt (fun y ↦ Finset.sum s (fun i ↦ f i y)) x := by
  -- Build the finite sum by repeatedly adding one locally Lipschitz summand at a time.
  induction s using Finset.cons_induction_on with
  | empty =>
      refine locallyLipschitzAt_iff.mpr ?_
      refine ⟨1, by norm_num, 0, ?_⟩
      intro y _ z _
      simp
  | cons i t hi ih =>
      have hi_local : LocallyLipschitzAt (f i) x :=
        h_local i (by simp)
      have ht_local : LocallyLipschitzAt (fun y ↦ Finset.sum t (fun j ↦ f j y)) x :=
        ih (fun j hj ↦ h_local j (by simp [hj]))
      -- The `Finset.cons` formula rewrites the larger finite sum as one new summand plus the tail.
      simpa [Finset.sum_cons, hi] using
        locallyLipschitzAt_add_real_of_locallyLipschitzAt hi_local ht_local

/-- A finite pointwise maximum of scalar fields that are `C¹` at `x` is locally Lipschitz at
`x`. -/
theorem locallyLipschitzAt_pointwiseMax_of_contDiffAt
    {ι : Type*}
    (s : Finset ι)
    (hs : s.Nonempty)
    (c : ι → E → ℝ)
    (x : E)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) :
    LocallyLipschitzAt (fun y ↦ s.sup' hs (fun i ↦ c i y)) x := by
  classical
  -- Reduce the finite `sup'` to repeated binary maxima and combine the branchwise witnesses.
  induction hs using Finset.Nonempty.cons_induction with
  | singleton i =>
      simpa [Finset.sup'_singleton] using (hC1 i (by simp)).locallyLipschitzAt
  | cons i t hi ht ih =>
      have hi_local : LocallyLipschitzAt (c i) x :=
        (hC1 i (by simp)).locallyLipschitzAt
      have ht_local : LocallyLipschitzAt (fun y ↦ t.sup' ht (fun j ↦ c j y)) x :=
        ih (fun j hj ↦ hC1 j (by simp [hj]))
      -- The recursive `sup'` formula rewrites the new finite maximum as a binary maximum.
      have hmax :
          LocallyLipschitzAt (fun y ↦ max (c i y) (t.sup' ht (fun j ↦ c j y))) x :=
        locallyLipschitzAt_max_of_locallyLipschitzAt hi_local ht_local
      have hsup :
          (fun y ↦ (insert i t).sup' (Finset.insert_nonempty i t) (fun j ↦ c j y)) =
            (fun y ↦ max (c i y) (t.sup' ht (fun j ↦ c j y))) := by
        funext y
        rw [Finset.sup'_insert]
      simpa [Finset.cons_eq_insert, hsup] using hmax

/-- A finite sum of absolute values of scalar fields that are `C¹` at `x` is locally Lipschitz
at `x`. -/
theorem locallyLipschitzAt_absoluteSum_of_contDiffAt
    {ι : Type*}
    (s : Finset ι)
    (c : ι → E → ℝ)
    (x : E)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) :
    LocallyLipschitzAt (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x := by
  -- Transfer the `C¹` hypothesis to each absolute-value summand, then sum the local witnesses.
  simpa using
    locallyLipschitzAt_finsetSum_of_locallyLipschitzAt s (fun i y ↦ |c i y|) x
      (fun i hi ↦ locallyLipschitzAt_abs_of_locallyLipschitzAt ((hC1 i hi).locallyLipschitzAt))

variable [CompleteSpace E]

/-- Helper for Chapter14 Exercise 14.4: if two scalar fields agree on a closed ball around `x`,
then their Clarke directional derivatives at `x` coincide in every direction. -/
theorem clarkeDirectionalDeriv_eq_of_eqOn_closedBall
    {f g : E → ℝ} {x d : E} {ε : ℝ}
    (hε : 0 < ε)
    (hEq : Set.EqOn f g (Metric.closedBall x ε)) :
    fᵒ(x; d) = gᵒ(x; d) := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let qf : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  let qg : E × ℝ → EReal :=
    fun p ↦ (((g (p.1 + p.2 • d) - g p.1) / p.2 : ℝ) : EReal)
  have hmem :
      ∀ᶠ p in l,
        p.1 ∈ Metric.closedBall x (ε / 2) ∧ p.1 + p.2 • d ∈ Metric.closedBall x (ε / 2) := by
    -- Keep both endpoints of the Clarke quotient inside the region where `f` and `g` agree.
    simpa [l] using
      eventuallyMemClosedBallEndpoints_of_closedBallLipschitz x d (show 0 < ε / 2 by linarith)
  have hEqQuot : qf =ᶠ[l] qg := by
    -- On that common closed ball, the numerator agrees pointwise, so the quotients coincide.
    filter_upwards [hmem] with p hp
    have hp1 : p.1 ∈ Metric.closedBall x ε :=
      Metric.closedBall_subset_closedBall (show ε / 2 ≤ ε by linarith) hp.1
    have hp2 : p.1 + p.2 • d ∈ Metric.closedBall x ε :=
      Metric.closedBall_subset_closedBall (show ε / 2 ≤ ε by linarith) hp.2
    simp [qf, qg, hEq hp2, hEq hp1]
  -- The Clarke owner is the limsup of these quotients, so eventual equality gives the result.
  rw [clarkeDirectionalDeriv_eq_limsup, clarkeDirectionalDeriv_eq_limsup]
  simpa [l, qf, qg] using Filter.limsup_congr hEqQuot

/-- Helper for Chapter14 Exercise 14.4: if two scalar fields agree on a closed ball around `x`,
then their Clarke differentials at `x` also coincide. -/
theorem clarkeDifferential_eq_of_eqOn_closedBall
    {f g : E → ℝ} {x : E} {ε : ℝ}
    (hε : 0 < ε)
    (hEq : Set.EqOn f g (Metric.closedBall x ε)) :
    clarkeDifferential f x = clarkeDifferential g x := by
  ext ξ
  rw [mem_clarkeDifferential_iff, mem_clarkeDifferential_iff]
  constructor
  · intro hξ d
    simpa [clarkeDirectionalDeriv_eq_of_eqOn_closedBall (x := x) (d := d) hε hEq] using hξ d
  · intro hξ d
    simpa [clarkeDirectionalDeriv_eq_of_eqOn_closedBall (x := x) (d := d) hε hEq] using hξ d

/-- Helper for Chapter14 Exercise 14.4: the full Clarke pair quotient of a `C¹` scalar field
converges to the gradient pairing at the base point. -/
theorem contDiffAt_clarkeQuotient_tendsto_gradient
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    Filter.Tendsto
      (fun p : E × ℝ ↦ ((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ))
      (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d))
      (nhds ((toDual ℝ E (gradient f x)) d)) := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let φ : E × ℝ → E × E := fun p ↦ (p.1 + p.2 • d, p.1)
  let L : StrongDual ℝ E := toDual ℝ E (gradient f x)
  have hgrad : HasGradientAt f (gradient f x) x :=
    hf.differentiableAt_one.hasGradientAt
  have h_fderiv : fderiv ℝ f x = L := by
    simpa [L] using hgrad.hasFDerivAt.fderiv
  have hstrict : HasStrictFDerivAt f L x := by
    -- A `C¹` scalar field has the strict derivative represented by its gradient.
    simpa [h_fderiv] using hf.hasStrictFDerivAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0)
  have hφ : Filter.Tendsto φ l (nhds (x, x)) := by
    have hφ_cont : Continuous φ := by
      continuity
    have hφ_nhds : Filter.Tendsto φ (nhds ((x : E), (0 : ℝ))) (nhds (x, x)) := by
      simpa [φ] using
        ((hφ_cont.continuousAt : ContinuousAt φ ((x : E), (0 : ℝ))).tendsto)
    exact hφ_nhds.comp nhdsWithin_le_nhds
  have hcomp :
      (fun p : E × ℝ ↦ f ((φ p).1) - f ((φ p).2) - L ((φ p).1 - (φ p).2))
        =o[l] fun p : E × ℝ ↦ (φ p).1 - (φ p).2 :=
    hstrict.isLittleO.comp_tendsto hφ
  have hbig :
      (fun p : E × ℝ ↦ (φ p).1 - (φ p).2) =O[l] fun p : E × ℝ ↦ p.2 := by
    have hsmul :
        Asymptotics.IsBigOWith ‖d‖ l (fun p : E × ℝ ↦ p.2 • d) fun p : E × ℝ ↦ p.2 := by
      refine Asymptotics.isBigOWith_of_le' l ?_
      intro p
      simp [norm_smul, Real.norm_eq_abs, mul_comm]
    simpa [φ] using hsmul.isBigO
  have hremainder :
      (fun p : E × ℝ ↦ f (p.1 + p.2 • d) - f p.1 - p.2 * L d) =o[l] fun p : E × ℝ ↦ p.2 := by
    -- Rewrite the strict-derivative remainder along the affine step `(p.1, p.2)`.
    simpa [φ, L.map_smul, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc] using
      hcomp.trans_isBigO hbig
  obtain ⟨ψ, hψ_tendsto, hψ_eq⟩ := hremainder.exists_eq_mul
  have hpos : ∀ᶠ p : E × ℝ in l, 0 < p.2 := by
    -- The Clarke pair filter only sees positive time increments.
    filter_upwards [self_mem_nhdsWithin] with p hp
    exact (mem_clarkeDirectionalDerivWithinDomain.mp hp).2.1
  have hquot_eq :
      (fun p : E × ℝ ↦ ((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ)) =ᶠ[l]
        fun p ↦ ψ p + L d := by
    -- Divide the strict-derivative expansion by the positive scalar `p.2`.
    filter_upwards [hψ_eq, hpos] with p hp hp2
    have hp2_ne : p.2 ≠ 0 := ne_of_gt hp2
    have hp' : f (p.1 + p.2 • d) - f p.1 - p.2 * L d = ψ p * p.2 := by
      simpa using hp
    have hp_mul : f (p.1 + p.2 • d) - f p.1 = p.2 * (ψ p + L d) := by
      calc
        f (p.1 + p.2 • d) - f p.1 = ψ p * p.2 + p.2 * L d := by
          exact sub_eq_iff_eq_add.mp hp'
        _ = p.2 * (ψ p + L d) := by ring
    rw [hp_mul, mul_div_cancel_left₀ _ hp2_ne]
  -- The quotient is an eventually-equal perturbation of `ψ + L d`, and `ψ → 0`.
  refine Filter.Tendsto.congr' hquot_eq.symm ?_
  simpa [L, add_comm] using hψ_tendsto.const_add ((toDual ℝ E (gradient f x)) d)

section pointwiseMax

variable {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (c : ι → E → ℝ) (x : E)

/-- Helper for Chapter14 Exercise 14.4: an active index attains the finite maximum at `x`. -/
theorem sup'_eq_of_mem_activeIndices
    {i : ι} (hi : i ∈ activeIndices s c x) :
    s.sup' hs (fun j ↦ c j x) = c i x := by
  -- The active-index inequalities give the upper bound, while the owner finset gives the lower
  -- bound by evaluating the supremum at the active branch itself.
  refine le_antisymm ?_ ?_
  · exact Finset.sup'_le hs (fun j ↦ c j x) (fun j hj ↦ hi.2 j hj)
  · exact Finset.le_sup'_of_le (s := s) (f := fun j ↦ c j x) hi.1 le_rfl

/-- Helper for Chapter14 Exercise 14.4: an inactive branch stays strictly below the active-branch
supremum on a sufficiently small closed ball around `x`, once the active branches are packaged in
an explicit finset selector `sA`. -/
theorem inactive_branch_lt_activeSup_on_closedBall
    {sA : Finset ι}
    (hsA : sA.Nonempty)
    (hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x)
    {j : ι}
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x)
    (hj : j ∈ s)
    (hjInactive : j ∉ activeIndices s c x) :
    ∃ ε > 0, ∀ y ∈ Metric.closedBall x ε,
      c j y < sA.sup' hsA (fun i ↦ c i y) := by
  have hsA' : sA.Nonempty := hsA
  rcases hsA with ⟨i0, hi0⟩
  have hi0Active : i0 ∈ activeIndices s c x := (hsA_active i0).1 hi0
  have hj_le_i0 : c j x ≤ c i0 x := hi0Active.2 j hj
  have hj_ne_i0 : c j x ≠ c i0 x := by
    intro hEq
    apply hjInactive
    refine ⟨hj, ?_⟩
    intro k hk
    have hk_le_i0 : c k x ≤ c i0 x := hi0Active.2 k hk
    simpa [hEq] using hk_le_i0
  have hj_lt_i0 : c j x < c i0 x := lt_of_le_of_ne hj_le_i0 hj_ne_i0
  let δ : ℝ := (c i0 x - c j x) / 4
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith
  have hcontj : ContinuousAt (c j) x := (hC1 j hj).continuousAt
  have hconti0 : ContinuousAt (c i0) x := (hC1 i0 hi0Active.1).continuousAt
  have hNj :
      Metric.closedBall (c j x) δ ∈ nhds (c j x) := Metric.closedBall_mem_nhds (c j x) hδ
  have hNi :
      Metric.closedBall (c i0 x) δ ∈ nhds (c i0 x) := Metric.closedBall_mem_nhds (c i0 x) hδ
  have hNj_pre :
      {y : E | c j y ∈ Metric.closedBall (c j x) δ} ∈ nhds x := hcontj hNj
  have hNi_pre :
      {y : E | c i0 y ∈ Metric.closedBall (c i0 x) δ} ∈ nhds x := hconti0 hNi
  obtain ⟨εj, hεj, hεjball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hNj_pre
  obtain ⟨εi, hεi, hεiball⟩ := Metric.nhds_basis_closedBall.mem_iff.1 hNi_pre
  let ε : ℝ := min εj εi
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min hεj hεi
  refine ⟨ε, hε, ?_⟩
  intro y hy
  have hyj : c j y ∈ Metric.closedBall (c j x) δ := by
    apply hεjball
    exact Metric.closedBall_subset_closedBall (min_le_left _ _) hy
  have hyi0 : c i0 y ∈ Metric.closedBall (c i0 x) δ := by
    apply hεiball
    exact Metric.closedBall_subset_closedBall (min_le_right _ _) hy
  have hj_bound : |c j y - c j x| ≤ δ := by
    simpa [Real.dist_eq] using Metric.mem_closedBall.mp hyj
  have hi0_bound : |c i0 y - c i0 x| ≤ δ := by
    simpa [Real.dist_eq] using Metric.mem_closedBall.mp hyi0
  have hj_upper : c j y ≤ c j x + δ := by
    have h := abs_le.mp hj_bound
    linarith
  have hi0_lower : c i0 x - δ ≤ c i0 y := by
    have h := abs_le.mp hi0_bound
    linarith
  have hgap : c j x + δ < c i0 x - δ := by
    dsimp [δ]
    linarith
  have hj_lt_i0_y : c j y < c i0 y := by
    linarith
  have hi0_le_activeSup :
      c i0 y ≤ sA.sup' hsA' (fun i ↦ c i y) :=
    Finset.le_sup'_of_le (s := sA) (f := fun i ↦ c i y) hi0 le_rfl
  exact lt_of_lt_of_le hj_lt_i0_y hi0_le_activeSup

/-- Helper for Chapter14 Exercise 14.4: once an explicit selector `sA` captures exactly the active
indices at `x`, the finite maximum is realized by `sA` on a small closed ball around `x`. -/
theorem pointwiseMax_eq_activeSup_on_closedBall
    [DecidableEq ι]
    {sA : Finset ι}
    (hsA : sA.Nonempty)
    (hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) :
    ∃ ε > 0, ∀ y ∈ Metric.closedBall x ε,
      s.sup' hs (fun j ↦ c j y) = sA.sup' hsA (fun i ↦ c i y) := by
  let t : Finset ι := s.filter (fun j ↦ j ∉ sA)
  by_cases ht : t.Nonempty
  · have hInactiveData :
        ∀ j : ↑t, ∃ ε > 0, ∀ y ∈ Metric.closedBall x ε, c j y < sA.sup' hsA (fun i ↦ c i y) := by
      intro j
      have hj_mem_t : j.1 ∈ t := j.2
      have hj_data : j.1 ∈ s ∧ j.1 ∉ sA := Finset.mem_filter.mp hj_mem_t
      have hj_mem_s : j.1 ∈ s := hj_data.1
      have hj_not_mem_sA : j.1 ∉ sA := hj_data.2
      have hj_inactive : j.1 ∉ activeIndices s c x := by
        intro hjActive
        exact hj_not_mem_sA ((hsA_active j).2 hjActive)
      exact inactive_branch_lt_activeSup_on_closedBall
        (sA := sA) (j := j.1) (hsA := hsA) (hsA_active := hsA_active)
        (hC1 := hC1) (hj := hj_mem_s) (hjInactive := hj_inactive)
    choose ε hε hInactive using hInactiveData
    letI : Nonempty ↑t := ht.to_subtype
    let δ : ℝ := Finset.univ.inf' Finset.univ_nonempty ε
    have hδ : 0 < δ := (Finset.lt_inf'_iff _).2 fun j _ ↦ hε j
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    have hmax_le_active :
        s.sup' hs (fun j ↦ c j y) ≤ sA.sup' hsA (fun i ↦ c i y) := by
      refine Finset.sup'_le hs (fun j ↦ c j y) (fun j hj ↦ ?_)
      by_cases hj_mem_sA : j ∈ sA
      · exact Finset.le_sup'_of_le (s := sA) (f := fun i ↦ c i y) hj_mem_sA le_rfl
      · have hj_mem_t : j ∈ t := by
          simpa [t, Finset.mem_filter] using And.intro hj hj_mem_sA
        let j' : ↑t := ⟨j, hj_mem_t⟩
        have hyj : y ∈ Metric.closedBall x (ε j') := by
          exact Metric.closedBall_subset_closedBall (Finset.inf'_le _ (Finset.mem_univ j')) hy
        exact (hInactive j' y hyj).le
    have hactive_le_max :
        sA.sup' hsA (fun i ↦ c i y) ≤ s.sup' hs (fun j ↦ c j y) := by
      refine Finset.sup'_le hsA (fun i ↦ c i y) (fun i hi ↦ ?_)
      have hi_mem_s : i ∈ s := (hsA_active i).1 hi |>.1
      exact Finset.le_sup'_of_le (s := s) (f := fun j ↦ c j y) hi_mem_s le_rfl
    exact le_antisymm hmax_le_active hactive_le_max
  · have hsA_eq : sA = s := by
      ext j
      constructor
      · intro hj
        exact ((hsA_active j).1 hj).1
      · intro hj
        by_contra hj_not_mem_sA
        exact ht ⟨j, by simpa [t, Finset.mem_filter] using And.intro hj hj_not_mem_sA⟩
    refine ⟨1, zero_lt_one, ?_⟩
    intro y hy
    simpa [hsA_eq]

/-- Helper for Chapter14 Exercise 14.4: after rewriting the nearby finite maximum by an explicit
active selector, the fixed-base quotient is eventually bounded by the selector supremum of the
branch quotients. -/
theorem pointwiseMax_constantBaseQuotient_eventually_le_active_selector_sup
    [DecidableEq ι]
    {sA : Finset ι}
    (hsA : sA.Nonempty)
    (hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x)
    (d : E) :
    ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      ((s.sup' hs (fun j ↦ c j (x + t • d)) - s.sup' hs (fun j ↦ c j x)) / t : ℝ) ≤
        sA.sup' hsA (fun i ↦ ((c i (x + t • d) - c i x) / t : ℝ)) := by
  rcases pointwiseMax_eq_activeSup_on_closedBall
      (s := s) (hs := hs) (c := c) (x := x)
      (sA := sA) hsA hsA_active hC1 with ⟨ε, hε, hactive_eq⟩
  have hball :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), x + t • d ∈ Metric.closedBall x ε := by
    have hsmul : ContinuousAt (fun t : ℝ ↦ t • d) (0 : ℝ) :=
      (continuous_id.smul continuous_const).continuousAt
    have hcont : ContinuousAt (fun t : ℝ ↦ x + t • d) (0 : ℝ) :=
      -- The source-faithful active-selector formula applies once the line segment stays in the
      -- closed ball where inactive branches remain dominated.
      continuous_const.continuousAt.add hsmul
    have hmem_pre :
        (fun t : ℝ ↦ x + t • d) ⁻¹'
            Metric.closedBall ((fun t : ℝ ↦ x + t • d) 0) ε ∈ nhds (0 : ℝ) :=
      hcont (Metric.closedBall_mem_nhds ((fun t : ℝ ↦ x + t • d) 0) hε)
    have hmem : {t : ℝ | x + t • d ∈ Metric.closedBall x ε} ∈ nhds (0 : ℝ) := by
      simpa [Set.preimage, zero_smul] using hmem_pre
    exact nhdsWithin_le_nhds hmem
  filter_upwards [self_mem_nhdsWithin, hball] with t ht hy
  have hnear_eq : s.sup' hs (fun j ↦ c j (x + t • d)) = sA.sup' hsA (fun i ↦ c i (x + t • d)) :=
    hactive_eq (x + t • d) hy
  have hbase_eq : s.sup' hs (fun j ↦ c j x) = sA.sup' hsA (fun i ↦ c i x) :=
    hactive_eq x (Metric.mem_closedBall_self hε.le)
  rcases Finset.exists_mem_eq_sup' hsA (fun i ↦ c i (x + t • d)) with ⟨i_t, hi_t, hi_t_eq⟩
  have hbase_ge : c i_t x ≤ sA.sup' hsA (fun i ↦ c i x) :=
    Finset.le_sup'_of_le (s := sA) (f := fun i ↦ c i x) hi_t le_rfl
  have hnum_le :
      sA.sup' hsA (fun i ↦ c i (x + t • d)) - sA.sup' hsA (fun i ↦ c i x) ≤
        c i_t (x + t • d) - c i_t x := by
    -- Choose the active branch attaining the nearby selector supremum and compare with the base
    -- selector supremum, which is at least the same branch evaluated at `x`.
    rw [hi_t_eq]
    linarith
  have hdiv_le :
      ((sA.sup' hsA (fun i ↦ c i (x + t • d)) - sA.sup' hsA (fun i ↦ c i x)) / t : ℝ) ≤
        ((c i_t (x + t • d) - c i_t x) / t : ℝ) := by
    -- Positive times preserve the inequality after dividing the fixed-base quotient by `t`.
    exact div_le_div_of_nonneg_right hnum_le ht.le
  calc
    ((s.sup' hs (fun j ↦ c j (x + t • d)) - s.sup' hs (fun j ↦ c j x)) / t : ℝ)
        = ((sA.sup' hsA (fun i ↦ c i (x + t • d)) - sA.sup' hsA (fun i ↦ c i x)) / t : ℝ) := by
            rw [hnear_eq, hbase_eq]
    _ ≤ ((c i_t (x + t • d) - c i_t x) / t : ℝ) := hdiv_le
    _ ≤ sA.sup' hsA (fun i ↦ ((c i (x + t • d) - c i x) / t : ℝ)) := by
          exact Finset.le_sup'_of_le
            (s := sA)
            (f := fun i ↦ ((c i (x + t • d) - c i x) / t : ℝ))
            hi_t le_rfl

/-- Helper for Chapter14 Exercise 14.4: the constant-base quotient limsup is always dominated by
the full Clarke directional derivative, because the constant-base path is one admissible Clarke
sampling route. -/
theorem constantBaseQuotient_limsup_le_clarkeDirectionalDeriv
    (f : E → ℝ) (x d : E) :
    Filter.limsup
        (fun t : ℝ ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      ≤ fᵒ(x; d) := by
  let u : E × ℝ → EReal :=
    fun p ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)
  let v : ℝ → E × ℝ := fun t ↦ ((x : E), t)
  have hv :
      Filter.Tendsto v
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)) := by
    -- The fixed-base embedding tends to the Clarke pair base point and preserves the positivity
    -- condition on the time variable.
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within v ?_ ?_
    · simpa [v] using
        Filter.Tendsto.prodMk_nhds
          (tendsto_const_nhds : Filter.Tendsto (fun _ : ℝ ↦ (x : E))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (x : E)))
          (tendsto_nhds_of_tendsto_nhdsWithin Filter.tendsto_id)
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact ⟨by simp, ht, by simp⟩
  have hcomp :
      u ∘ v = fun t : ℝ ↦ (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
    -- Evaluating the Clarke quotient along the constant-base path gives the announced quotient.
    funext t
    simp [u, v, Function.comp]
  -- Compare the constant-base limsup with the full Clarke limsup through the admissible
  -- embedding `t ↦ (x, t)`.
  rw [clarkeDirectionalDeriv_eq_limsup]
  rw [← hcomp]
  simpa [u, v] using
    (hv.limsup_comp_le_limsup (β := EReal) (u := u))

/-- Helper for Chapter14 Exercise 14.4: on the full Clarke pair filter, once the nearby finite
maximum is controlled by an explicit active selector `sA`, its quotient is bounded above by the
selector supremum of the branch quotients. -/
theorem pointwiseMax_clarkeQuotient_eventually_le_active_selector_sup
    [DecidableEq ι]
    {sA : Finset ι}
    (hsA : sA.Nonempty)
    (hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x)
    (d : E) :
    ∀ᶠ p in nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d),
      (((s.sup' hs (fun j ↦ c j (p.1 + p.2 • d)) - s.sup' hs (fun j ↦ c j p.1)) / p.2 : ℝ) ≤
        sA.sup' hsA (fun i ↦ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ))) := by
  rcases pointwiseMax_eq_activeSup_on_closedBall
      (s := s) (hs := hs) (c := c) (x := x)
      (sA := sA) hsA hsA_active hC1 with ⟨ε, hε, hactive_eq⟩
  have hmem :
      ∀ᶠ p in
          nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d),
        p.1 ∈ Metric.closedBall x (ε / 2) ∧
          p.1 + p.2 • d ∈ Metric.closedBall x (ε / 2) := by
    -- Keep both endpoints inside the closed ball where the active-selector description holds.
    simpa using
      eventuallyMemClosedBallEndpoints_of_closedBallLipschitz x d
        (show 0 < ε / 2 by linarith)
  filter_upwards [self_mem_nhdsWithin, hmem] with p hp hp_mem
  have hp_pos : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hp).2.1
  have hy :
      p.1 ∈ Metric.closedBall x ε :=
    Metric.closedBall_subset_closedBall (show ε / 2 ≤ ε by linarith) hp_mem.1
  have hstep :
      p.1 + p.2 • d ∈ Metric.closedBall x ε :=
    Metric.closedBall_subset_closedBall (show ε / 2 ≤ ε by linarith) hp_mem.2
  have htop :
      s.sup' hs (fun j ↦ c j (p.1 + p.2 • d)) =
        sA.sup' hsA (fun i ↦ c i (p.1 + p.2 • d)) :=
    hactive_eq _ hstep
  have hbase :
      s.sup' hs (fun j ↦ c j p.1) =
        sA.sup' hsA (fun i ↦ c i p.1) :=
    hactive_eq _ hy
  rcases Finset.exists_mem_eq_sup' hsA (fun i ↦ c i (p.1 + p.2 • d)) with ⟨i, hi, hi_eq⟩
  have hbase_ge : c i p.1 ≤ sA.sup' hsA (fun j ↦ c j p.1) :=
    Finset.le_sup'_of_le (s := sA) (f := fun j ↦ c j p.1) hi le_rfl
  have hnum_le :
      sA.sup' hsA (fun i ↦ c i (p.1 + p.2 • d)) - sA.sup' hsA (fun i ↦ c i p.1) ≤
        c i (p.1 + p.2 • d) - c i p.1 := by
    -- Choose the branch attaining the top selector value at the stepped point.
    rw [hi_eq]
    linarith
  have hdiv_le :
      ((sA.sup' hsA (fun i ↦ c i (p.1 + p.2 • d)) - sA.sup' hsA (fun i ↦ c i p.1)) / p.2 : ℝ) ≤
        ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ) := by
    exact div_le_div_of_nonneg_right hnum_le hp_pos.le
  calc
    (((s.sup' hs (fun j ↦ c j (p.1 + p.2 • d)) - s.sup' hs (fun j ↦ c j p.1)) / p.2 : ℝ))
        = ((sA.sup' hsA (fun i ↦ c i (p.1 + p.2 • d)) - sA.sup' hsA (fun i ↦ c i p.1)) / p.2 :
            ℝ) := by
            rw [htop, hbase]
    _ ≤ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ) := hdiv_le
    _ ≤ sA.sup' hsA (fun j ↦ ((c j (p.1 + p.2 • d) - c j p.1) / p.2 : ℝ)) := by
          exact Finset.le_sup'_of_le
            (s := sA)
            (f := fun j ↦ ((c j (p.1 + p.2 • d) - c j p.1) / p.2 : ℝ))
            hi
            le_rfl

/-- Helper for Chapter14 Exercise 14.4: the Clarke directional derivative of the finite maximum
is bounded by the support function of the active gradients at `x`. -/
theorem clarkeDirectionalDerivReal_pointwiseMax_le_active_sup
    [DecidableEq ι]
    {sA : Finset ι}
    (hsA : sA.Nonempty)
    (hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x)
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x)
    (d : E) :
    clarkeDirectionalDerivReal (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d ≤
      sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let qMax : E × ℝ → EReal :=
    fun p ↦
      ((((s.sup' hs (fun j ↦ c j (p.1 + p.2 • d))) - (s.sup' hs (fun j ↦ c j p.1))) / p.2 : ℝ) :
        EReal)
  let qSup : E × ℝ → EReal :=
    fun p ↦
      ((sA.sup' hsA (fun i ↦ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ)) : ℝ) : EReal)
  have hqMax_le :
      qMax ≤ᶠ[l] qSup := by
    -- The full pair quotient of the maximum is eventually dominated by the selector supremum.
    filter_upwards
      [pointwiseMax_clarkeQuotient_eventually_le_active_selector_sup
        (s := s) (hs := hs) (c := c) (x := x)
        (sA := sA) hsA hsA_active hC1 d] with p hp
    change
      ((((s.sup' hs (fun j ↦ c j (p.1 + p.2 • d))) - (s.sup' hs (fun j ↦ c j p.1))) / p.2 : ℝ) :
        EReal) ≤
        (((sA.sup' hsA (fun i ↦ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ)) : ℝ)) : EReal)
    exact_mod_cast hp
  have hbranch :
      ∀ i ∈ sA,
        Filter.Tendsto
          (fun p : E × ℝ ↦ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ))
          l
          (nhds ((toDual ℝ E (gradient (c i) x)) d)) := by
    intro i hi
    -- Each active branch is smooth, so its full pair quotient tends to the gradient pairing.
    exact contDiffAt_clarkeQuotient_tendsto_gradient
      ((hC1 i ((hsA_active i).1 hi).1))
  have hqSup_tendsto :
      Filter.Tendsto
        (fun p : E × ℝ ↦ sA.sup' hsA (fun i ↦ ((c i (p.1 + p.2 • d) - c i p.1) / p.2 : ℝ)))
        l
        (nhds (sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d))) := by
    -- The finite supremum preserves convergence along the common Clarke pair filter.
    exact Filter.Tendsto.finset_sup'_nhds_apply hsA hbranch
  have hqSup_tendstoE :
      Filter.Tendsto qSup l
        (nhds (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal)) := by
    exact (EReal.tendsto_coe).2 hqSup_tendsto
  have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hqMax_limsup_le :
      Filter.limsup qMax l ≤
        (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) := by
    calc
      Filter.limsup qMax l ≤ Filter.limsup qSup l := Filter.limsup_le_limsup hqMax_le
      _ = (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) := by
          simpa [qSup] using hqSup_tendstoE.limsup_eq
  have hlocal :
      LocallyLipschitzAt (fun y ↦ s.sup' hs (fun j ↦ c j y)) x :=
    locallyLipschitzAt_pointwiseMax_of_contDiffAt s hs c x hC1
  have hrealE :
      (((clarkeDirectionalDerivReal (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d : ℝ)) : EReal) ≤
        (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) := by
    calc
      (((clarkeDirectionalDerivReal (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d : ℝ)) : EReal)
          = (fun y ↦ s.sup' hs (fun j ↦ c j y))ᵒ(x; d) := by
            rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
              (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d hlocal]
      _ = Filter.limsup qMax l := by
            simpa [qMax, l] using
              (clarkeDirectionalDeriv_eq_limsup (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d)
      _ ≤ (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) :=
        hqMax_limsup_le
  exact_mod_cast hrealE

/-- Helper for Chapter14 Exercise 14.4: every active branch gradient is already a Clarke
generalized gradient of the finite pointwise maximum. This is the direct source-faithful
forward inclusion, obtained from the fixed-base directional quotients. -/
theorem active_gradient_mem_clarkeDifferential_pointwiseMax
    {i : ι}
    (hC1 : ∀ j ∈ s, ContDiffAt ℝ 1 (c j) x)
    (hi : i ∈ activeIndices s c x) :
    toDual ℝ E (gradient (c i) x) ∈
      clarkeDifferential (fun y ↦ s.sup' hs (fun j ↦ c j y)) x := by
  rw [mem_clarkeDifferential_iff]
  intro d
  change
    ((((toDual ℝ E (gradient (c i) x)) d : ℝ) : EReal) ≤
      (fun y ↦ s.sup' hs (fun j ↦ c j y))ᵒ(x; d))
  let qBranch : ℝ → EReal :=
    fun t ↦ (((c i (x + t • d) - c i x) / t : ℝ) : EReal)
  let qMax : ℝ → EReal :=
    fun t ↦
      ((((s.sup' hs (fun j ↦ c j (x + t • d))) - (s.sup' hs (fun j ↦ c j x))) / t : ℝ) : EReal)
  have hline :
      HasLineDerivAt ℝ (c i) ((toDual ℝ E (gradient (c i) x)) d) x d := by
    -- The active branch is smooth, so its line derivative in direction `d` is the gradient
    -- pairing `⟪∇ c_i(x), d⟫`.
    simpa using
      ((hC1 i hi.1).differentiableAt_one.hasGradientAt.hasFDerivAt.hasLineDerivAt d)
  have hslopeReal :
      Filter.Tendsto
        (fun t : ℝ ↦ t⁻¹ * (c i (x + t • d) - c i x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((toDual ℝ E (gradient (c i) x)) d)) := by
    -- The smooth branch quotient tends to the gradient pairing in the usual real topology.
    simpa using hline.tendsto_slope_zero_right
  have hslope :
      Filter.Tendsto
        (fun t : ℝ ↦ ((t⁻¹ * (c i (x + t • d) - c i x) : ℝ) : EReal))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((((toDual ℝ E (gradient (c i) x)) d : ℝ) : EReal))) := by
    -- Cast the real slope limit to `EReal` once, then reuse it as the branch limsup identity.
    exact (EReal.tendsto_coe).2 hslopeReal
  have hqBranch_eq_slope :
      qBranch =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t : ℝ ↦ ((t⁻¹ * (c i (x + t • d) - c i x) : ℝ) : EReal) := by
    -- On the positive-time filter, the explicit quotient is exactly the normalized slope form
    -- used by `HasLineDerivAt.tendsto_slope_zero_right`.
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_ne : t ≠ 0 := ne_of_gt ht
    simp [qBranch, div_eq_mul_inv, mul_comm, ht_ne, zero_smul]
  have hqBranch_tendsto :
      Filter.Tendsto qBranch (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (((toDual ℝ E (gradient (c i) x)) d : ℝ) : EReal)) := by
    refine Filter.Tendsto.congr' hqBranch_eq_slope.symm hslope
  have hqBranch_le :
      qBranch ≤ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] qMax := by
    -- Active equality at the base point turns the pointwise branch domination into a quotient
    -- domination along the fixed-base path.
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    have hbranch_le :
        c i (x + t • d) ≤ s.sup' hs (fun j ↦ c j (x + t • d)) :=
      Finset.le_sup'_of_le (s := s) (f := fun j ↦ c j (x + t • d)) hi.1 le_rfl
    have hnum_le :
        c i (x + t • d) - c i x ≤
          s.sup' hs (fun j ↦ c j (x + t • d)) - s.sup' hs (fun j ↦ c j x) := by
      rw [sup'_eq_of_mem_activeIndices (s := s) (hs := hs) (c := c) (x := x) hi]
      exact sub_le_sub_right hbranch_le _
    have hdiv_le :
        (c i (x + t • d) - c i x) / t ≤
          ((s.sup' hs (fun j ↦ c j (x + t • d))) - (s.sup' hs (fun j ↦ c j x))) / t := by
      exact div_le_div_of_nonneg_right hnum_le ht_pos.le
    change
      ((((c i (x + t • d) - c i x) / t : ℝ) : EReal) ≤
        ((((s.sup' hs (fun j ↦ c j (x + t • d))) - (s.sup' hs (fun j ↦ c j x))) / t : ℝ) :
          EReal))
    exact_mod_cast hdiv_le
  have hqBranch_limsup_le :
      Filter.limsup qBranch (nhdsWithin (0 : ℝ) (Set.Ioi 0)) ≤
        Filter.limsup qMax (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
    exact Filter.limsup_le_limsup hqBranch_le
  have hqBranch_limsup_eq :
      Filter.limsup qBranch (nhdsWithin (0 : ℝ) (Set.Ioi 0)) =
        (((toDual ℝ E (gradient (c i) x)) d : ℝ) : EReal) := by
    simpa [qBranch] using hqBranch_tendsto.limsup_eq
  -- The branch limit is below the fixed-base max limsup, and that limsup is below the full
  -- Clarke directional derivative of the maximum.
  calc
    (((toDual ℝ E (gradient (c i) x)) d : ℝ) : EReal) =
        Filter.limsup qBranch (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
          symm
          exact hqBranch_limsup_eq
    _ ≤ Filter.limsup qMax (nhdsWithin (0 : ℝ) (Set.Ioi 0)) :=
      hqBranch_limsup_le
    _ ≤ (fun y ↦ s.sup' hs (fun j ↦ c j y))ᵒ(x; d) := by
      simpa [qMax] using
        constantBaseQuotient_limsup_le_clarkeDirectionalDeriv
          (f := fun y ↦ s.sup' hs (fun j ↦ c j y)) x d

/-- The Clarke differential bridge for a finite pointwise maximum at `x`, with the local
Lipschitz witness supplied by pointwise `C¹` regularity of the family members at `x`. -/
abbrev clarkeDifferentialOfPointwiseMax
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) : Set DualPoint :=
  letI : LocallyLipschitzAt (fun y ↦ s.sup' hs (fun i ↦ c i y)) x :=
    locallyLipschitzAt_pointwiseMax_of_contDiffAt s hs c x hC1
  clarkeDifferential (fun y ↦ s.sup' hs (fun i ↦ c i y)) x

/-- Chapter14 Exercise 14.4 (1): if `c i` is continuously differentiable at `x` for every
`i` in a nonempty finite family `s` and `f(x) = max_(i ∈ s) c i x`, then the Clarke
differential `∂ f(x)` is the convex hull of the active gradients `∇ c_i(x)` at the indices
attaining the maximum value. -/
theorem clarkeDifferential_pointwiseMax
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) :
    clarkeDifferentialOfPointwiseMax s hs c x hC1 =
      convexHull ℝ
        ((fun i ↦ toDual ℝ E (gradient (c i) x)) '' activeIndices s c x)
      := by
  classical
  let sA : Finset ι := s.filter (fun i ↦ i ∈ activeIndices s c x)
  have hsA : sA.Nonempty := by
    rcases activeIndices_nonempty (E := E) s hs c x with ⟨i, hi⟩
    exact ⟨i, by simpa [sA, Finset.mem_filter] using And.intro hi.1 hi⟩
  have hsA_active : ∀ i, i ∈ sA ↔ i ∈ activeIndices s c x := by
    intro i
    constructor
    · intro hi
      exact (Finset.mem_filter.mp hi).2
    · intro hi
      exact Finset.mem_filter.mpr ⟨hi.1, hi⟩
  have hlocal :
      LocallyLipschitzAt (fun y ↦ s.sup' hs (fun j ↦ c j y)) x :=
    locallyLipschitzAt_pointwiseMax_of_contDiffAt s hs c x hC1
  apply Set.Subset.antisymm
  · intro ξ hξ
    let activeGradients : Set DualPoint :=
      ((fun i ↦ toDual ℝ E (gradient (c i) x)) '' activeIndices s c x)
    let S : Set WeakDualPoint := StrongDual.toWeakDual '' convexHull ℝ activeGradients
    have h_conv : Convex ℝ S := by
      -- Push the convex hull through the weak-dual embedding to reach the halfspace criterion.
      simpa [S, activeGradients] using
        (convex_convexHull ℝ activeGradients).linear_image
          ((StrongDual.toWeakDual : DualPoint ≃ₗ[ℝ] WeakDualPoint).toLinearMap)
    have h_closed : IsClosed S := by
      -- The finite active-gradient hull is compact, hence its weak-dual image is closed.
      have hfinite : activeGradients.Finite :=
        finite_activeGradients (E := E) s c x
      have hcompact :
          IsCompact (convexHull ℝ activeGradients) :=
        hfinite.isCompact_convexHull (𝕜 := ℝ)
      simpa [S] using
        (hcompact.image NormedSpace.Dual.toWeakDual_continuous).isClosed
    have hξ_mem : StrongDual.toWeakDual ξ ∈ S := by
      rw [mem_closed_convex_iff_eval_halfspaces h_conv h_closed]
      intro d
      have hsupport :
          ξ d ≤ sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) := by
        have hξE : (((ξ d : ℝ)) : EReal) ≤ (fun y ↦ s.sup' hs (fun j ↦ c j y))ᵒ(x; d) :=
          (mem_clarkeDifferential_iff (fun y ↦ s.sup' hs (fun j ↦ c j y)) x ξ).1 hξ d
        have hsupE :
            (((ξ d : ℝ)) : EReal) ≤
              (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) := by
          calc
            (((ξ d : ℝ)) : EReal) ≤ (fun y ↦ s.sup' hs (fun j ↦ c j y))ᵒ(x; d) := hξE
            _ = (((clarkeDirectionalDerivReal (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d : ℝ)) :
                  EReal) := by
                  symm
                  exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
                    (fun y ↦ s.sup' hs (fun j ↦ c j y)) x d hlocal
            _ ≤ (((sA.sup' hsA (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) : ℝ)) : EReal) := by
                  exact_mod_cast clarkeDirectionalDerivReal_pointwiseMax_le_active_sup
                    (s := s) (hs := hs) (c := c) (x := x)
                    (sA := sA) hsA hsA_active hC1 d
        exact_mod_cast hsupE
      rcases Finset.exists_mem_eq_sup' hsA
          (fun i ↦ (toDual ℝ E (gradient (c i) x)) d) with ⟨i, hi, hi_eq⟩
      refine ⟨StrongDual.toWeakDual (toDual ℝ E (gradient (c i) x)), ?_, ?_⟩
      · refine ⟨toDual ℝ E (gradient (c i) x), ?_, rfl⟩
        refine subset_convexHull ℝ activeGradients ?_
        exact ⟨i, (hsA_active i).1 hi, rfl⟩
      · change ξ d ≤ (toDual ℝ E (gradient (c i) x)) d
        have hsup_eq :
            sA.sup' hsA (fun j ↦ (toDual ℝ E (gradient (c j) x)) d) =
              (toDual ℝ E (gradient (c i) x)) d := by
          simpa using hi_eq
        rw [← hsup_eq]
        exact hsupport
    rcases hξ_mem with ⟨η, hη, hηeq⟩
    exact (StrongDual.toWeakDual_inj _ _).1 hηeq ▸ hη
  · -- Every active gradient belongs to the Clarke differential, and convexity closes the hull.
    refine convexHull_min ?_ ?_
    · rintro _ ⟨i, hi, rfl⟩
      exact active_gradient_mem_clarkeDifferential_pointwiseMax
        (s := s) (hs := hs) (c := c) (x := x) hC1 hi
    · simpa [clarkeDifferentialOfPointwiseMax] using
        convex_clarkeDifferential_local_of_locallyLipschitzAt
          (fun y ↦ s.sup' hs (fun j ↦ c j y)) x hlocal

end pointwiseMax

section absoluteSum

variable {ι : Type*} (s : Finset ι) (c : ι → E → ℝ) (x : E)

/-- The Clarke differential bridge for the finite absolute-sum functional at `x`, with the local
Lipschitz witness supplied by pointwise `C¹` regularity of the summands at `x`. -/
abbrev clarkeDifferentialOfAbsoluteSum
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) : Set DualPoint :=
  letI : LocallyLipschitzAt (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x :=
    locallyLipschitzAt_absoluteSum_of_contDiffAt s c x hC1
  clarkeDifferential (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x

/-- Helper for Chapter14 Exercise 14.4: the fixed-base quotient of a `C¹` scalar field along the
ray `x + t • d` converges to the gradient pairing. -/
theorem contDiffAt_constantBaseQuotient_tendsto_gradient
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    Filter.Tendsto
      (fun t : ℝ ↦ ((f (x + t • d) - f x) / t : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((toDual ℝ E (gradient f x)) d)) := by
  have hline :
      HasLineDerivAt ℝ f ((toDual ℝ E (gradient f x)) d) x d := by
    -- A `C¹` branch differentiates along every line with derivative given by its gradient.
    simpa using
      hf.differentiableAt_one.hasGradientAt.hasFDerivAt.hasLineDerivAt d
  -- Repackage the line-derivative slope limit into the explicit quotient used in the exercise.
  simpa [div_eq_mul_inv, mul_comm] using hline.tendsto_slope_zero_right

/-- Helper for Chapter14 Exercise 14.4: if `f x > 0`, then the absolute-value quotient agrees
with the branch quotient near `x`, so it converges to the gradient pairing. -/
theorem abs_comp_constantBaseQuotient_tendsto_pos
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) (hx : 0 < f x) :
    Filter.Tendsto
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((toDual ℝ E (gradient f x)) d)) := by
  have hstep : ContinuousAt (fun t : ℝ ↦ x + t • d) (0 : ℝ) :=
    continuous_const.continuousAt.add (continuous_id.smul continuous_const).continuousAt
  have hstep_tendsto :
      Filter.Tendsto (fun t : ℝ ↦ x + t • d)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds x) := by
    simpa [zero_smul] using hstep.tendsto.mono_left nhdsWithin_le_nhds
  have hline :
      Filter.Tendsto (fun t : ℝ ↦ f (x + t • d))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (f x)) := by
    exact hf.continuousAt.tendsto.comp hstep_tendsto
  have hEventuallyPos :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < f (x + t • d) := by
    -- Continuity keeps the branch on the same positive side for sufficiently small `t > 0`.
    exact hline (Ioi_mem_nhds hx)
  have hEventuallyEq :
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t : ℝ ↦ ((f (x + t • d) - f x) / t : ℝ) := by
    -- Once both base and nearby values are positive, `|f|` is just `f`.
    filter_upwards [hEventuallyPos] with t ht_pos
    simp [abs_of_pos hx, abs_of_pos ht_pos]
  -- Replace the absolute-value quotient by the smooth branch quotient and reuse the slope limit.
  exact Filter.Tendsto.congr' hEventuallyEq.symm
    (contDiffAt_constantBaseQuotient_tendsto_gradient hf)

/-- Helper for Chapter14 Exercise 14.4: if `f x < 0`, then the absolute-value quotient agrees
with the quotient of `-f` near `x`, so it converges to the negated gradient pairing. -/
theorem abs_comp_constantBaseQuotient_tendsto_neg
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) (hx : f x < 0) :
    Filter.Tendsto
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds (-((toDual ℝ E (gradient f x)) d))) := by
  have hstep : ContinuousAt (fun t : ℝ ↦ x + t • d) (0 : ℝ) :=
    continuous_const.continuousAt.add (continuous_id.smul continuous_const).continuousAt
  have hstep_tendsto :
      Filter.Tendsto (fun t : ℝ ↦ x + t • d)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds x) := by
    simpa [zero_smul] using hstep.tendsto.mono_left nhdsWithin_le_nhds
  have hline :
      Filter.Tendsto (fun t : ℝ ↦ f (x + t • d))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (f x)) := by
    exact hf.continuousAt.tendsto.comp hstep_tendsto
  have hEventuallyNeg :
      ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), f (x + t • d) < 0 := by
    -- Continuity keeps the branch on the same negative side for sufficiently small `t > 0`.
    exact hline (Iio_mem_nhds hx)
  have hEventuallyEq :
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t : ℝ ↦ -((f (x + t • d) - f x) / t : ℝ) := by
    -- On the negative branch, `|f| = -f`, so the quotient picks up one global minus sign.
    filter_upwards [hEventuallyNeg] with t ht_neg
    have hrewrite :
        ((-f (x + t • d) - -f x) / t : ℝ) = -((f (x + t • d) - f x) / t : ℝ) := by
      ring
    simpa [abs_of_neg hx, abs_of_neg ht_neg] using hrewrite
  have hneg :
      Filter.Tendsto
        (fun t : ℝ ↦ -((f (x + t • d) - f x) / t : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-((toDual ℝ E (gradient f x)) d))) := by
    -- Negation commutes with taking limits in the scalar codomain.
    exact Filter.Tendsto.neg (contDiffAt_constantBaseQuotient_tendsto_gradient hf)
  exact Filter.Tendsto.congr' hEventuallyEq.symm hneg

/-- Helper for Chapter14 Exercise 14.4: if `f x = 0`, then the absolute-value quotient is the
absolute value of the branch quotient, so it converges to the absolute gradient pairing. -/
theorem abs_comp_constantBaseQuotient_tendsto_zero
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) (hx : f x = 0) :
    Filter.Tendsto
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds |(toDual ℝ E (gradient f x)) d|) := by
  have hEventuallyEq :
      (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ)) =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t : ℝ ↦ |((f (x + t • d) - f x) / t : ℝ)| := by
    -- At a zero base value and positive times, the absolute quotient is exactly the absolute
    -- value of the branch quotient.
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht_pos : 0 < t := ht
    simp [hx, abs_div, abs_of_pos ht_pos]
  have habs :
      Filter.Tendsto
        (fun t : ℝ ↦ |((f (x + t • d) - f x) / t : ℝ)|)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds |(toDual ℝ E (gradient f x)) d|) := by
    -- Absolute value is continuous on `ℝ`, so it preserves the branch-quotient limit.
    exact Filter.Tendsto.abs (contDiffAt_constantBaseQuotient_tendsto_gradient hf)
  exact Filter.Tendsto.congr' hEventuallyEq.symm habs

/-- Helper for Chapter14 Exercise 14.4: the fixed-base quotient of `|f|` tends to the support
value dictated by the sign of `f x`. -/
theorem abs_comp_constantBaseQuotient_tendsto_support
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    (0 < f x →
      Filter.Tendsto
        (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds ((toDual ℝ E (gradient f x)) d))) ∧
    (f x < 0 →
      Filter.Tendsto
        (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds (-((toDual ℝ E (gradient f x)) d)))) ∧
    (f x = 0 →
      Filter.Tendsto
        (fun t : ℝ ↦ ((|f (x + t • d)| - |f x|) / t : ℝ))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds |(toDual ℝ E (gradient f x)) d|)) := by
  constructor
  · intro hx
    -- Positive base values use the stable positive branch.
    exact abs_comp_constantBaseQuotient_tendsto_pos hf hx
  constructor
  · intro hx
    -- Negative base values use the stable negative branch.
    exact abs_comp_constantBaseQuotient_tendsto_neg hf hx
  · intro hx
    -- Zero base values collapse to the absolute-value limit of the smooth quotient.
    exact abs_comp_constantBaseQuotient_tendsto_zero hf hx

/-- Helper for Chapter14 Exercise 14.4: for a `C¹` scalar field, the Clarke directional
derivative is exactly the gradient pairing. -/
theorem clarkeDirectionalDerivReal_eq_gradient_of_contDiffAt
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    clarkeDirectionalDerivReal f x d = (toDual ℝ E (gradient f x)) d := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hlocal : LocallyLipschitzAt f x := hf.locallyLipschitzAt
  have hlim :
      Filter.Tendsto
        (fun p : E × ℝ ↦ (((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
        l
        (nhds ((((toDual ℝ E (gradient f x)) d : ℝ)) : EReal)) := by
    exact (EReal.tendsto_coe).2 (contDiffAt_clarkeQuotient_tendsto_gradient (x := x) (d := d) hf)
  -- Rewrite the canonical Clarke owner as the limsup of the smooth quotient, then read off the
  -- limit value.
  have hE :
      (((clarkeDirectionalDerivReal f x d : ℝ)) : EReal) =
        ((((toDual ℝ E (gradient f x)) d : ℝ)) : EReal) := by
    rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d hlocal, clarkeDirectionalDeriv_eq_limsup]
    simpa [l] using hlim.limsup_eq
  exact_mod_cast hE

/-- Helper for Chapter14 Exercise 14.4: for a `C¹` scalar field, negating the branch negates the
Clarke directional derivative. -/
theorem clarkeDirectionalDerivReal_neg_of_contDiffAt
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    clarkeDirectionalDerivReal (fun y ↦ -f y) x d = -((toDual ℝ E (gradient f x)) d) := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let qneg : E × ℝ → EReal :=
    fun p ↦ ((((-f (p.1 + p.2 • d)) - (-f p.1)) / p.2 : ℝ) : EReal)
  have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
  letI := hl_ne
  have hlocal : LocallyLipschitzAt (fun y ↦ -f y) x := by
    rcases locallyLipschitzAt_iff.mp hf.locallyLipschitzAt with ⟨ε, hε, K, hK⟩
    refine locallyLipschitzAt_iff.mpr ⟨ε, hε, K, ?_⟩
    refine LipschitzOnWith.of_dist_le_mul
      (s := Metric.closedBall x ε)
      (f := fun y ↦ -f y)
      (K := K) fun y hy z hz ↦ ?_
    simpa using hK.dist_le_mul y hy z hz
  have hqneg_eq :
      qneg =ᶠ[l] fun p ↦ -((((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)) := by
    -- Pointwise, the quotient of `-f` is just the negated quotient of `f`.
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp_ne : p.2 ≠ 0 := ne_of_gt (mem_clarkeDirectionalDerivWithinDomain.mp hp).2.1
    have hreal :
        (((-f (p.1 + p.2 • d)) - (-f p.1)) / p.2 : ℝ) =
          -((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) := by
      field_simp [hp_ne]
      ring
    change ((((-f (p.1 + p.2 • d)) - (-f p.1)) / p.2 : ℝ) : EReal) =
      -((((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))
    rw [hreal]
    simp
  have hlim :
      Filter.Tendsto
        (fun p : E × ℝ ↦ -((((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal)))
        l
        (nhds (((-((toDual ℝ E (gradient f x)) d) : ℝ)) : EReal)) := by
    -- Transport the smooth-quotient limit through negation.
    simpa using
      (EReal.tendsto_coe).2
        (Filter.Tendsto.neg (contDiffAt_clarkeQuotient_tendsto_gradient (x := x) (d := d) hf))
  -- The Clarke limsup for `-f` is the limsup of this negated quotient.
  have hE :
      (((clarkeDirectionalDerivReal (fun y ↦ -f y) x d : ℝ)) : EReal) =
        (((-((toDual ℝ E (gradient f x)) d) : ℝ)) : EReal) := by
    rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ -f y) x d hlocal,
      clarkeDirectionalDeriv_eq_limsup]
    calc
      Filter.limsup qneg l =
          Filter.limsup
            (fun p ↦ -((((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ) : EReal))) l := by
              exact Filter.limsup_congr hqneg_eq
      _ = (((-((toDual ℝ E (gradient f x)) d) : ℝ)) : EReal) := by
            simpa [l] using hlim.limsup_eq
  exact_mod_cast hE

/-- Helper for Chapter14 Exercise 14.4: the Clarke directional derivative of `|f|` is the
branch support selected by the sign of `f x`. -/
theorem clarkeDirectionalDerivReal_abs_eq_branchSupport
    {f : E → ℝ} {x d : E} (hf : ContDiffAt ℝ 1 f x) :
    clarkeDirectionalDerivReal (fun y ↦ |f y|) x d =
      if 0 < f x then
        (toDual ℝ E (gradient f x)) d
      else if f x < 0 then
        -((toDual ℝ E (gradient f x)) d)
      else
        |(toDual ℝ E (gradient f x)) d| := by
  by_cases hpos : 0 < f x
  · have hlocal_abs : LocallyLipschitzAt (fun y ↦ |f y|) x :=
      locallyLipschitzAt_abs_of_locallyLipschitzAt hf.locallyLipschitzAt
    have hpos_pre : {y : E | 0 < f y} ∈ nhds x :=
      hf.continuousAt (Ioi_mem_nhds hpos)
    rcases Metric.nhds_basis_closedBall.mem_iff.1 hpos_pre with ⟨ε, hε, hεball⟩
    have hEq : Set.EqOn (fun y ↦ |f y|) f (Metric.closedBall x ε) := by
      intro y hy
      have hy_pos : 0 < f y := by simpa using hεball hy
      simp [abs_of_pos hy_pos]
    -- On a neighborhood where `f` stays positive, `|f|` is exactly `f`.
    have hE :
        (((clarkeDirectionalDerivReal (fun y ↦ |f y|) x d : ℝ)) : EReal) =
          ((((toDual ℝ E (gradient f x)) d : ℝ)) : EReal) := by
      rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ |f y|) x d hlocal_abs]
      rw [clarkeDirectionalDeriv_eq_of_eqOn_closedBall (x := x) (d := d) hε hEq]
      rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt f x d hf.locallyLipschitzAt]
      exact_mod_cast clarkeDirectionalDerivReal_eq_gradient_of_contDiffAt (x := x) (d := d) hf
    have hreal :
        clarkeDirectionalDerivReal (fun y ↦ |f y|) x d = (toDual ℝ E (gradient f x)) d := by
      exact_mod_cast hE
    simpa [hpos] using hreal
  · by_cases hneg : f x < 0
    · have hlocal_abs : LocallyLipschitzAt (fun y ↦ |f y|) x :=
        locallyLipschitzAt_abs_of_locallyLipschitzAt hf.locallyLipschitzAt
      have hlocal_neg : LocallyLipschitzAt (fun y ↦ -f y) x := by
        rcases locallyLipschitzAt_iff.mp hf.locallyLipschitzAt with ⟨ε', hε', K, hK⟩
        refine locallyLipschitzAt_iff.mpr ⟨ε', hε', K, ?_⟩
        refine LipschitzOnWith.of_dist_le_mul
          (s := Metric.closedBall x ε')
          (f := fun y ↦ -f y)
          (K := K) fun y hy z hz ↦ ?_
        simpa using hK.dist_le_mul y hy z hz
      have hneg_pre : {y : E | f y < 0} ∈ nhds x :=
        hf.continuousAt (Iio_mem_nhds hneg)
      rcases Metric.nhds_basis_closedBall.mem_iff.1 hneg_pre with ⟨ε, hε, hεball⟩
      have hEq : Set.EqOn (fun y ↦ |f y|) (fun y ↦ -f y) (Metric.closedBall x ε) := by
        intro y hy
        have hy_neg : f y < 0 := by simpa using hεball hy
        simp [abs_of_neg hy_neg]
      -- On a neighborhood where `f` stays negative, `|f|` is exactly `-f`.
      have hE :
          (((clarkeDirectionalDerivReal (fun y ↦ |f y|) x d : ℝ)) : EReal) =
            (((-((toDual ℝ E (gradient f x)) d) : ℝ)) : EReal) := by
        rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ |f y|) x d hlocal_abs]
        rw [clarkeDirectionalDeriv_eq_of_eqOn_closedBall (x := x) (d := d) hε hEq]
        rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ -f y) x d hlocal_neg]
        exact_mod_cast clarkeDirectionalDerivReal_neg_of_contDiffAt (x := x) (d := d) hf
      have hreal :
          clarkeDirectionalDerivReal (fun y ↦ |f y|) x d = -((toDual ℝ E (gradient f x)) d) := by
        exact_mod_cast hE
      simpa [hpos, hneg] using hreal
    · have hzero : f x = 0 := by linarith
      have hlocal_abs : LocallyLipschitzAt (fun y ↦ |f y|) x :=
        locallyLipschitzAt_abs_of_locallyLipschitzAt hf.locallyLipschitzAt
      let l : Filter (E × ℝ) :=
        nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
      let qabs : E × ℝ → EReal :=
        fun p ↦ (((|f (p.1 + p.2 • d)| - |f p.1|) / p.2 : ℝ) : EReal)
      let qfAbs : E × ℝ → EReal :=
        fun p ↦ ((|((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ)| : ℝ) : EReal)
      have hl_ne : l.NeBot := wholeSpaceClarkePairFilter_neBot x d
      letI := hl_ne
      have hqabs_le : qabs ≤ᶠ[l] qfAbs := by
        -- The reverse triangle inequality bounds the absolute-value quotient by the absolute
        -- value of the smooth quotient on the whole Clarke pair filter.
        filter_upwards [self_mem_nhdsWithin] with p hp
        have hp_pos : 0 < p.2 := (mem_clarkeDirectionalDerivWithinDomain.mp hp).2.1
        have hnum :
            |f (p.1 + p.2 • d)| - |f p.1| ≤ |f (p.1 + p.2 • d) - f p.1| := by
          exact (abs_le.mp (abs_abs_sub_abs_le_abs_sub (f (p.1 + p.2 • d)) (f p.1))).2
        have hreal :
            ((|f (p.1 + p.2 • d)| - |f p.1|) / p.2 : ℝ) ≤
              |((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ)| := by
          calc
            ((|f (p.1 + p.2 • d)| - |f p.1|) / p.2 : ℝ)
                ≤ |f (p.1 + p.2 • d) - f p.1| / p.2 := by
                    exact div_le_div_of_nonneg_right hnum hp_pos.le
              _ = |((f (p.1 + p.2 • d) - f p.1) / p.2 : ℝ)| := by
                  rw [abs_div, abs_of_pos hp_pos]
        dsimp [qabs, qfAbs]
        exact_mod_cast hreal
      have hqfAbs_tendsto :
          Filter.Tendsto qfAbs l
            (nhds ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal)) := by
        -- The smooth quotient tends to the gradient pairing, and absolute value is continuous.
        simpa [qfAbs, l] using
          (EReal.tendsto_coe).2
            (Filter.Tendsto.abs (contDiffAt_clarkeQuotient_tendsto_gradient (x := x) (d := d) hf))
      have hupperE :
          (((clarkeDirectionalDerivReal (fun y ↦ |f y|) x d : ℝ)) : EReal) ≤
            ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal) := by
        rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ |f y|) x d hlocal_abs,
          clarkeDirectionalDeriv_eq_limsup]
        calc
          Filter.limsup qabs l ≤ Filter.limsup qfAbs l := Filter.limsup_le_limsup hqabs_le
          _ = ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal) := by
                simpa [l] using hqfAbs_tendsto.limsup_eq
      have hconst_tendsto :
          Filter.Tendsto
            (fun t : ℝ ↦
              ((|f (x + t • d)| - |f x|) / t : ℝ))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))
            (nhds |(toDual ℝ E (gradient f x)) d|) :=
        (abs_comp_constantBaseQuotient_tendsto_support (x := x) (d := d) hf).2.2 hzero
      have hconstE :
          Filter.limsup
              (fun t : ℝ ↦
                ((((|f (x + t • d)| - |f x|) / t : ℝ)) : EReal))
              (nhdsWithin (0 : ℝ) (Set.Ioi 0)) =
            ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal) := by
        simpa using ((EReal.tendsto_coe).2 hconst_tendsto).limsup_eq
      have hlowerE :
          ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal) ≤
            (((clarkeDirectionalDerivReal (fun y ↦ |f y|) x d : ℝ)) : EReal) := by
        calc
          ((((|(toDual ℝ E (gradient f x)) d| : ℝ))) : EReal) =
              Filter.limsup
                (fun t : ℝ ↦
                  ((((|f (x + t • d)| - |f x|) / t : ℝ)) : EReal))
                (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
                  symm
                  exact hconstE
          _ ≤ (fun y ↦ |f y|)ᵒ(x; d) := by
                simpa using
                  constantBaseQuotient_limsup_le_clarkeDirectionalDeriv (f := fun y ↦ |f y|) x d
          _ = (((clarkeDirectionalDerivReal (fun y ↦ |f y|) x d : ℝ)) : EReal) := by
                symm
                exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
                  (fun y ↦ |f y|) x d hlocal_abs
      -- The lower bound comes from the fixed-base quotient, while the upper bound comes from the
      -- full Clarke quotient estimate.
      have hupper :
          clarkeDirectionalDerivReal (fun y ↦ |f y|) x d ≤ |(toDual ℝ E (gradient f x)) d| := by
        exact_mod_cast hupperE
      have hlower :
          |(toDual ℝ E (gradient f x)) d| ≤ clarkeDirectionalDerivReal (fun y ↦ |f y|) x d := by
        exact_mod_cast hlowerE
      simpa [hpos, hneg] using le_antisymm hupper hlower

/-- Helper for Chapter14 Exercise 14.4: the coefficient box is the product of the coordinate
singleton or interval constraints dictated by the signs of `c i x`. -/
theorem absoluteSumCoefficients_eq_pi :
    absoluteSumCoefficients s c x =
      Set.pi Set.univ
        (fun i : ↑s ↦
          if 0 < c i x then
            ({1} : Set ℝ)
          else if c i x < 0 then
            ({-1} : Set ℝ)
          else
            Set.Icc (-1 : ℝ) 1) := by
  ext μ
  constructor
  · intro hμ
    rcases hμ with ⟨hpos, hneg, hzero⟩
    intro i _
    by_cases hi_pos : 0 < c i x
    · simpa [hi_pos, hpos i hi_pos]
    · by_cases hi_neg : c i x < 0
      · simpa [hi_pos, hi_neg, hneg i hi_neg]
      · have hi_zero : c i x = 0 := by linarith
        simpa [hi_pos, hi_neg, hi_zero] using hzero i hi_zero
  · intro hμ
    refine ⟨?_, ?_, ?_⟩
    · intro i hi_pos
      have hi_mem := hμ i (by simp)
      simpa [hi_pos] using hi_mem
    · intro i hi_neg
      have hi_mem := hμ i (by simp)
      have hi_not_pos : ¬ 0 < c i x := not_lt.mpr hi_neg.le
      simpa [hi_not_pos, hi_neg] using hi_mem
    · intro i hi_zero
      have hi_mem := hμ i (by simp)
      have hi_not_pos : ¬ 0 < c i x := by simpa [hi_zero]
      have hi_not_neg : ¬ c i x < 0 := by simpa [hi_zero]
      simpa [hi_not_pos, hi_not_neg, hi_zero] using hi_mem

/-- Helper for Chapter14 Exercise 14.4: the coefficient box is convex because each coordinate is
either a singleton or the interval `[-1, 1]`. -/
theorem convex_absoluteSumCoefficients :
    Convex ℝ (absoluteSumCoefficients s c x) := by
  rw [absoluteSumCoefficients_eq_pi (s := s) (c := c) (x := x)]
  refine convex_pi ?_
  intro i _
  by_cases hi_pos : 0 < c i x
  · simp [hi_pos, convex_singleton]
  · by_cases hi_neg : c i x < 0
    · simp [hi_pos, hi_neg, convex_singleton]
    · simp [hi_pos, hi_neg, convex_Icc]

/-- Helper for Chapter14 Exercise 14.4: the coefficient box is compact, as it is a finite product
of compact singleton or interval factors. -/
theorem isCompact_absoluteSumCoefficients :
    IsCompact (absoluteSumCoefficients s c x) := by
  rw [absoluteSumCoefficients_eq_pi (s := s) (c := c) (x := x)]
  refine isCompact_univ_pi ?_
  intro i
  by_cases hi_pos : 0 < c i x
  · simp [hi_pos, isCompact_singleton]
  · by_cases hi_neg : c i x < 0
    · simp [hi_pos, hi_neg, isCompact_singleton]
    · simp [hi_pos, hi_neg, isCompact_Icc]

/-- Helper for Chapter14 Exercise 14.4: the Clarke directional derivative of a sum of two locally
Lipschitz scalar maps is bounded by the sum of the two support values. -/
lemma clarkeDirectionalDerivReal_add_le
    (u v : E → ℝ) (x d : E)
    (hu : LocallyLipschitzAt u x) (hv : LocallyLipschitzAt v x) :
    clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d ≤
      clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d := by
  let l : Filter (E × ℝ) :=
    nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)
  let quv : E × ℝ → EReal :=
    fun p ↦ ((((u (p.1 + p.2 • d) + v (p.1 + p.2 • d)) - (u p.1 + v p.1)) / p.2 : ℝ) : EReal)
  let qu : E × ℝ → EReal :=
    fun p ↦ (((u (p.1 + p.2 • d) - u p.1) / p.2 : ℝ) : EReal)
  let qv : E × ℝ → EReal :=
    fun p ↦ (((v (p.1 + p.2 • d) - v p.1) / p.2 : ℝ) : EReal)
  have hquv_eq : quv =ᶠ[l] fun p ↦ qu p + qv p := by
    -- Expand the quotient of a sum into the sum of the two quotients before taking limsups.
    filter_upwards [self_mem_nhdsWithin] with p hp
    have hp_ne : p.2 ≠ 0 := ne_of_gt (mem_clarkeDirectionalDerivWithinDomain.mp hp).2.1
    have hreal :
        (((u (p.1 + p.2 • d) + v (p.1 + p.2 • d)) - (u p.1 + v p.1)) / p.2 : ℝ) =
          ((u (p.1 + p.2 • d) - u p.1) / p.2 : ℝ) +
            ((v (p.1 + p.2 • d) - v p.1) / p.2 : ℝ) := by
      field_simp [hp_ne]
      ring
    change ((((u (p.1 + p.2 • d) + v (p.1 + p.2 • d)) - (u p.1 + v p.1)) / p.2 : ℝ) : EReal) =
      ((((u (p.1 + p.2 • d) - u p.1) / p.2 : ℝ) : EReal)) +
        ((((v (p.1 + p.2 • d) - v p.1) / p.2 : ℝ) : EReal))
    exact_mod_cast hreal
  have hquv_limsup :
      Filter.limsup quv l = (fun y ↦ u y + v y)ᵒ(x; d) := by
    simpa [l, quv] using (clarkeDirectionalDeriv_eq_limsup (fun y ↦ u y + v y) x d).symm
  have hqu_limsup : Filter.limsup qu l = uᵒ(x; d) := by
    simpa [l, qu] using (clarkeDirectionalDeriv_eq_limsup u x d).symm
  have hqv_limsup : Filter.limsup qv l = vᵒ(x; d) := by
    simpa [l, qv] using (clarkeDirectionalDeriv_eq_limsup v x d).symm
  have hqu_ne_top : Filter.limsup qu l ≠ ⊤ := by
    simpa [hqu_limsup] using (clarkeDirectionalDeriv_ne_top_ne_bot_of_locallyLipschitzAt u x d hu).1
  have hqu_ne_bot : Filter.limsup qu l ≠ ⊥ := by
    simpa [hqu_limsup] using (clarkeDirectionalDeriv_ne_top_ne_bot_of_locallyLipschitzAt u x d hu).2
  have hsum :
      (fun y ↦ u y + v y)ᵒ(x; d) ≤ uᵒ(x; d) + vᵒ(x; d) := by
    calc
      (fun y ↦ u y + v y)ᵒ(x; d) = Filter.limsup quv l := hquv_limsup.symm
      _ = Filter.limsup (fun p ↦ qu p + qv p) l := by
            exact Filter.limsup_congr hquv_eq
      _ ≤ Filter.limsup qu l + Filter.limsup qv l := by
            exact EReal.limsup_add_le (Or.inl hqu_ne_bot) (Or.inl hqu_ne_top)
      _ = uᵒ(x; d) + vᵒ(x; d) := by rw [hqu_limsup, hqv_limsup]
  have huv : LocallyLipschitzAt (fun y ↦ u y + v y) x :=
    locallyLipschitzAt_add_real_of_locallyLipschitzAt hu hv
  -- Convert the canonical `EReal` inequality back to the real-valued textbook surface.
  have hsum_real :
      (((clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d : ℝ)) : EReal) ≤
        (((clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
    calc
      (((clarkeDirectionalDerivReal (fun y ↦ u y + v y) x d : ℝ)) : EReal)
          = (fun y ↦ u y + v y)ᵒ(x; d) := by
              rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun y ↦ u y + v y) x d huv]
      _ ≤ uᵒ(x; d) + vᵒ(x; d) := hsum
      _ = (((clarkeDirectionalDerivReal u x d : ℝ)) : EReal) +
            (((clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
              rw [← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt u x d hu,
                ← coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt v x d hv]
      _ = (((clarkeDirectionalDerivReal u x d + clarkeDirectionalDerivReal v x d : ℝ)) : EReal) := by
            norm_num
  exact_mod_cast hsum_real

/-- Helper for Chapter14 Exercise 14.4: the real-valued Clarke directional derivative of a finite
sum is bounded by the finite sum of the support values of the summands. -/
lemma clarkeDirectionalDerivReal_finsetSum_le
    {ι : Type*} (s : Finset ι) (f : ι → E → ℝ) (x d : E)
    (h_local : ∀ i ∈ s, LocallyLipschitzAt (f i) x) :
    clarkeDirectionalDerivReal (fun y ↦ s.sum fun i ↦ f i y) x d ≤
      s.sum (fun i ↦ clarkeDirectionalDerivReal (f i) x d) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hzero_local : LocallyLipschitzAt (fun _ : E ↦ (0 : ℝ)) x := by
        refine locallyLipschitzAt_iff.mpr ?_
        refine ⟨1, zero_lt_one, 0, ?_⟩
        intro y _ z _
        simp
      have hzero :
          clarkeDirectionalDerivReal (fun _ : E ↦ (0 : ℝ)) x d = 0 := by
        have hl_ne :
            (nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d)).NeBot :=
          wholeSpaceClarkePairFilter_neBot x d
        letI := hl_ne
        have hzeroE :
            (((clarkeDirectionalDerivReal (fun _ : E ↦ (0 : ℝ)) x d : ℝ)) : EReal) = 0 := by
          rw [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt (fun _ : E ↦ (0 : ℝ)) x d
            hzero_local]
          rw [clarkeDirectionalDeriv_eq_limsup]
          simpa using
            (Filter.limsup_const
              (f := nhdsWithin ((x : E), (0 : ℝ)) (clarkeDirectionalDerivWithinDomain Set.univ d))
              (a := (0 : EReal)))
        exact_mod_cast hzeroE
      -- The empty sum is the constant zero function.
      simpa [hzero]
  | @insert i s hi hs =>
      have hi_local : LocallyLipschitzAt (f i) x := h_local i (by simp)
      have hs_local : ∀ j ∈ s, LocallyLipschitzAt (f j) x := by
        intro j hj
        exact h_local j (by simp [hj])
      have htail_local :
          LocallyLipschitzAt (fun y ↦ s.sum fun j ↦ f j y) x :=
        locallyLipschitzAt_finsetSum_of_locallyLipschitzAt s f x hs_local
      have hhead :
          clarkeDirectionalDerivReal
              (fun y ↦ f i y + s.sum (fun j ↦ f j y)) x d ≤
            clarkeDirectionalDerivReal (f i) x d +
              clarkeDirectionalDerivReal (fun y ↦ s.sum fun j ↦ f j y) x d :=
        clarkeDirectionalDerivReal_add_le (f i) (fun y ↦ s.sum fun j ↦ f j y) x d
          hi_local htail_local
      -- Split off one summand and apply the induction hypothesis to the tail.
      calc
        clarkeDirectionalDerivReal (fun y ↦ (insert i s).sum fun j ↦ f j y) x d
            = clarkeDirectionalDerivReal
                (fun y ↦ f i y + s.sum (fun j ↦ f j y)) x d := by
                  simp [Finset.sum_insert hi]
        _ ≤ clarkeDirectionalDerivReal (f i) x d +
              clarkeDirectionalDerivReal (fun y ↦ s.sum fun j ↦ f j y) x d := hhead
        _ ≤ clarkeDirectionalDerivReal (f i) x d +
              s.sum (fun j ↦ clarkeDirectionalDerivReal (f j) x d) := by
              exact add_le_add le_rfl (hs hs_local)
        _ = (insert i s).sum (fun j ↦ clarkeDirectionalDerivReal (f j) x d) := by
              simp [Finset.sum_insert hi]

/-- Helper for Chapter14 Exercise 14.4: the Clarke directional derivative of the finite absolute
sum is exactly the sum of the branch-support values of the summands. -/
theorem clarkeDirectionalDerivReal_absoluteSum_eq_support_sum
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) (d : E) :
    clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d =
      Finset.sum s (fun i ↦
        if 0 < c i x then
          (toDual ℝ E (gradient (c i) x)) d
        else if c i x < 0 then
          -((toDual ℝ E (gradient (c i) x)) d)
        else
          |(toDual ℝ E (gradient (c i) x)) d|) := by
  have hlocal_abs :
      ∀ i ∈ s, LocallyLipschitzAt (fun y ↦ |c i y|) x := by
    intro i hi
    exact locallyLipschitzAt_abs_of_locallyLipschitzAt ((hC1 i hi).locallyLipschitzAt)
  have hlocal_sum :
      LocallyLipschitzAt (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x :=
    locallyLipschitzAt_absoluteSum_of_contDiffAt s c x hC1
  have hupper :
      clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d ≤
        Finset.sum s (fun i ↦
          if 0 < c i x then
            (toDual ℝ E (gradient (c i) x)) d
          else if c i x < 0 then
            -((toDual ℝ E (gradient (c i) x)) d)
          else
            |(toDual ℝ E (gradient (c i) x)) d|) := by
    calc
      clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d
          ≤ Finset.sum s (fun i ↦ clarkeDirectionalDerivReal (fun y ↦ |c i y|) x d) := by
              exact clarkeDirectionalDerivReal_finsetSum_le s (fun i y ↦ |c i y|) x d hlocal_abs
      _ = Finset.sum s (fun i ↦
            if 0 < c i x then
              (toDual ℝ E (gradient (c i) x)) d
            else if c i x < 0 then
              -((toDual ℝ E (gradient (c i) x)) d)
            else
              |(toDual ℝ E (gradient (c i) x)) d|) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              exact clarkeDirectionalDerivReal_abs_eq_branchSupport (x := x) (d := d) (hC1 i hi)
  let qsum : ℝ → ℝ :=
    fun t ↦
      ((Finset.sum s (fun i ↦ |c i (x + t • d)|) - Finset.sum s (fun i ↦ |c i x|)) / t : ℝ)
  have hqsum_eq :
      qsum =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
        fun t ↦ Finset.sum s (fun i ↦ ((|c i (x + t • d)| - |c i x|) / t : ℝ)) := by
    -- The fixed-base quotient of the sum is the sum of the fixed-base quotients.
    filter_upwards [self_mem_nhdsWithin] with t ht
    change
      ((Finset.sum s (fun i ↦ |c i (x + t • d)|) - Finset.sum s (fun i ↦ |c i x|)) / t : ℝ) =
        Finset.sum s (fun i ↦ ((|c i (x + t • d)| - |c i x|) / t : ℝ))
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_div]
  let support : ℝ :=
    Finset.sum s (fun i ↦
      if 0 < c i x then
        (toDual ℝ E (gradient (c i) x)) d
      else if c i x < 0 then
        -((toDual ℝ E (gradient (c i) x)) d)
      else
        |(toDual ℝ E (gradient (c i) x)) d|)
  have hqsum_tendsto :
      Filter.Tendsto qsum (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (nhds support) := by
    refine Filter.Tendsto.congr' hqsum_eq.symm ?_
    exact tendsto_finsetSum _ fun i hi ↦ by
      rcases abs_comp_constantBaseQuotient_tendsto_support (x := x) (d := d) (hC1 i hi) with
        ⟨hpos, hneg, hzero⟩
      by_cases hi_pos : 0 < c i x
      · simpa [hi_pos] using hpos hi_pos
      · by_cases hi_neg : c i x < 0
        · simpa [hi_pos, hi_neg] using hneg hi_neg
        · have hi_zero : c i x = 0 := by linarith
          simpa [hi_pos, hi_neg, hi_zero] using hzero hi_zero
  have hqsumE :
      Filter.limsup (fun t ↦ ((qsum t : ℝ) : EReal)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) =
        ((support : ℝ) : EReal) := by
    simpa using ((EReal.tendsto_coe).2 hqsum_tendsto).limsup_eq
  have hlowerE :
      ((support : ℝ) : EReal) ≤
        (((clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d : ℝ)) : EReal) := by
    calc
      (((Finset.sum s (fun i ↦
          if 0 < c i x then
            (toDual ℝ E (gradient (c i) x)) d
          else if c i x < 0 then
            -((toDual ℝ E (gradient (c i) x)) d)
          else
            |(toDual ℝ E (gradient (c i) x)) d|) : ℝ)) : EReal) =
          Filter.limsup (fun t ↦ ((qsum t : ℝ) : EReal)) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) := by
            symm
            exact hqsumE
      _ ≤ (fun y ↦ Finset.sum s (fun i ↦ |c i y|))ᵒ(x; d) := by
            simpa [qsum] using
              constantBaseQuotient_limsup_le_clarkeDirectionalDeriv
                (f := fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d
      _ = (((clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d : ℝ)) : EReal) := by
            symm
            exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
              (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d hlocal_sum
  -- The fixed-base quotient lower bound and the full Clarke-sum upper bound meet at the same
  -- support value.
  have hlower :
      support ≤ clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d := by
    exact_mod_cast hlowerE
  simpa [support] using le_antisymm hupper hlower

/-- Chapter14 Exercise 14.4 (2): if `c i` is continuously differentiable at `x` for every
`i` in a finite family `s` and `f̄(x) = ∑_(i ∈ s) |c i x|`, then the Clarke differential
`∂ f̄(x)` consists of the finite combinations `∑_(i ∈ s) μ_i ∇ c_i(x)` for coefficient families
`μ : ↑s → ℝ`, where `μ_i = 1` when `c_i(x) > 0`, `μ_i = -1` when `c_i(x) < 0`, and
`μ_i ∈ [-1, 1]` when `c_i(x) = 0`. -/
theorem clarkeDifferential_absoluteSum
    (hC1 : ∀ i ∈ s, ContDiffAt ℝ 1 (c i) x) :
    clarkeDifferentialOfAbsoluteSum s c x hC1 =
      (fun μ : ↑s → ℝ ↦
        Finset.sum s.attach (fun i ↦ μ i • toDual ℝ E (gradient (c i) x))) ''
        absoluteSumCoefficients s c x := by
  classical
  let g : ↑s → DualPoint := fun i ↦ toDual ℝ E (gradient (c i) x)
  let targetStrong : (↑s → ℝ) → DualPoint :=
    fun μ ↦ Finset.sum s.attach (fun i ↦ μ i • g i)
  let targetWeak : (↑s → ℝ) → WeakDualPoint :=
    fun μ ↦ Finset.sum s.attach (fun i ↦ μ i • StrongDual.toWeakDual (g i))
  let S : Set WeakDualPoint := targetWeak '' absoluteSumCoefficients s c x
  have hlocal_sum :
      LocallyLipschitzAt (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x :=
    locallyLipschitzAt_absoluteSum_of_contDiffAt s c x hC1
  have hcoeff_conv : Convex ℝ (absoluteSumCoefficients s c x) :=
    convex_absoluteSumCoefficients (s := s) (c := c) (x := x)
  have htargetWeak_cont : Continuous targetWeak := by
    -- The target map is a finite sum of coordinate evaluations scaled by fixed gradients.
    refine continuous_finsetSum _ fun i _ ↦ ?_
    simpa [targetWeak] using
      (continuous_apply i).smul continuous_const
  have hS_conv : Convex ℝ S := by
    intro ξ hξ η hη a b ha hb hab
    rcases hξ with ⟨μ, hμ, rfl⟩
    rcases hη with ⟨ν, hν, rfl⟩
    refine ⟨a • μ + b • ν, hcoeff_conv hμ hν ha hb hab, ?_⟩
    -- The image map is affine-linear in the coefficient vector.
    apply (WeakDual.toStrongDual_inj _ _).mp
    ext d'
    simp [S, targetWeak, Finset.sum_add_distrib, add_smul, smul_smul, smul_eq_mul,
      Finset.mul_sum, mul_add, add_mul, mul_assoc, mul_comm, mul_left_comm]
  have hS_compact : IsCompact S := by
    simpa [S] using
      (isCompact_absoluteSumCoefficients (s := s) (c := c) (x := x)).image htargetWeak_cont
  have hS_closed : IsClosed S := hS_compact.isClosed
  apply Set.Subset.antisymm
  · intro ξ hξ
    have hξ_mem : StrongDual.toWeakDual ξ ∈ S := by
      rw [mem_closed_convex_iff_eval_halfspaces hS_conv hS_closed]
      intro d
      let μd : ↑s → ℝ := fun i ↦
        if 0 < c i x then
          1
        else if c i x < 0 then
          -1
        else if 0 ≤ g i d then
          1
        else
          -1
      have hμd : μd ∈ absoluteSumCoefficients s c x := by
        refine ⟨?_, ?_, ?_⟩
        · intro i hi_pos
          simp [μd, hi_pos, not_lt.mpr hi_pos.le]
        · intro i hi_neg
          have hi_not_pos : ¬ 0 < c i x := not_lt.mpr hi_neg.le
          simp [μd, hi_not_pos, hi_neg]
        · intro i hi_zero
          have hi_not_pos : ¬ 0 < c i x := by simpa [hi_zero]
          have hi_not_neg : ¬ c i x < 0 := by simpa [hi_zero]
          by_cases hgd : 0 ≤ g i d
          · simp [μd, hi_not_pos, hi_not_neg, hi_zero, hgd]
          · have hgd_lt : g i d < 0 := lt_of_not_ge hgd
            simp [μd, hi_not_pos, hi_not_neg, hi_zero, hgd, hgd_lt]
      refine ⟨targetWeak μd, ⟨μd, hμd, rfl⟩, ?_⟩
      have hξ_support :
          ξ d ≤ clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d := by
        -- Transport the generalized-gradient inequality to the real-valued support surface.
        have hξE :
            (((ξ d : ℝ)) : EReal) ≤
              (((clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d : ℝ)) :
                EReal) := by
          simpa [coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
            (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d hlocal_sum] using
            (mem_clarkeDifferential_iff (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x ξ).1 hξ d
        exact_mod_cast hξE
      have hμd_eval :
          targetWeak μd d =
            Finset.sum s.attach (fun i ↦
              if 0 < c i x then
                g i d
              else if c i x < 0 then
                -(g i d)
              else
                |g i d|) := by
        -- The chosen coefficient vector realizes the branch-support value coordinatewise.
        calc
          targetWeak μd d = Finset.sum s.attach (fun i ↦ (μd i • g i) d) := by
                change WeakDual.toStrongDual (targetWeak μd) d =
                  Finset.sum s.attach (fun i ↦ (μd i • g i) d)
                simp [targetWeak]
          _ = Finset.sum s.attach (fun i ↦ μd i * g i d) := by
                simp [smul_eq_mul]
          _ = Finset.sum s.attach (fun i ↦
                if 0 < c i x then
                  g i d
                else if c i x < 0 then
                  -(g i d)
                else
                  |g i d|) := by
                  refine Finset.sum_congr rfl ?_
                  intro i hi
                  by_cases hi_pos : 0 < c i x
                  · simp [targetWeak, μd, hi_pos, g, smul_eq_mul]
                  · by_cases hi_neg : c i x < 0
                    · simp [targetWeak, μd, hi_pos, hi_neg, g, smul_eq_mul]
                    · have hi_zero : c i x = 0 := by linarith
                      by_cases hgd : 0 ≤ g i d
                      · simp [μd, hi_pos, hi_neg, hi_zero, hgd, abs_of_nonneg hgd]
                      · have hgd_lt : g i d < 0 := lt_of_not_ge hgd
                        simp [μd, hi_pos, hi_neg, hi_zero, hgd, hgd_lt, abs_of_neg hgd_lt]
      calc
        (StrongDual.toWeakDual ξ) d = ξ d := by rfl
        _ ≤ clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d := hξ_support
        _ = Finset.sum s.attach (fun i ↦
              if 0 < c i x then
                g i d
              else if c i x < 0 then
                -(g i d)
              else
                |g i d|) := by
              have hsupport_attach :
                  clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d =
                    Finset.sum s.attach (fun i ↦
                      if 0 < c i x then
                        g i d
                      else if c i x < 0 then
                        -(g i d)
                      else
                        |g i d|) := by
                    calc
                      clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d =
                          Finset.sum s (fun i ↦
                            if 0 < c i x then
                              (toDual ℝ E (gradient (c i) x)) d
                            else if c i x < 0 then
                              -((toDual ℝ E (gradient (c i) x)) d)
                            else
                              |(toDual ℝ E (gradient (c i) x)) d|) := by
                            exact clarkeDirectionalDerivReal_absoluteSum_eq_support_sum
                              (s := s) (c := c) (x := x) hC1 d
                      _ = Finset.sum s.attach (fun i ↦
                            if 0 < c i x then
                              g i d
                            else if c i x < 0 then
                              -(g i d)
                            else
                              |g i d|) := by
                            simpa [g] using
                              (Finset.sum_attach (s := s) (f := fun i ↦
                                if 0 < c i x then
                                  (toDual ℝ E (gradient (c i) x)) d
                                else if c i x < 0 then
                                  -((toDual ℝ E (gradient (c i) x)) d)
                                else
                                  |(toDual ℝ E (gradient (c i) x)) d|)).symm
              exact hsupport_attach
        _ = targetWeak μd d := hμd_eval.symm
    rcases hξ_mem with ⟨μ, hμ, hμeq⟩
    have hstrong_eq :
        targetStrong μ = ξ := by
      apply (StrongDual.toWeakDual_inj _ _).1
      simpa [targetStrong, targetWeak, g] using hμeq
    exact ⟨μ, hμ, hstrong_eq⟩
  · rintro ξ ⟨μ, hμ, rfl⟩
    rw [mem_clarkeDifferential_iff]
    intro d
    have hscalar :
        ∀ i : ↑s,
          μ i * g i d ≤
            if 0 < c i x then
              g i d
            else if c i x < 0 then
              -(g i d)
            else
              |g i d| := by
      intro i
      rcases hμ with ⟨hpos, hneg, hzero⟩
      by_cases hi_pos : 0 < c i x
      · simp [g, hi_pos, hpos i hi_pos]
      · by_cases hi_neg : c i x < 0
        · have hi_not_pos : ¬ 0 < c i x := not_lt.mpr hi_neg.le
          simp [g, hi_not_pos, hi_neg, hneg i hi_neg]
        · have hi_zero : c i x = 0 := by linarith
          have hμIcc : μ i ∈ Set.Icc (-1 : ℝ) 1 := hzero i hi_zero
          have hμabs : |μ i| ≤ 1 := by
            rcases hμIcc with ⟨hlo, hhi⟩
            exact abs_le.mpr ⟨by linarith, by linarith⟩
          calc
            μ i * g i d ≤ |μ i * g i d| := le_abs_self _
            _ = |μ i| * |g i d| := by rw [abs_mul]
            _ ≤ 1 * |g i d| := by
                  exact mul_le_mul_of_nonneg_right hμabs (abs_nonneg _)
            _ = |g i d| := by ring
            _ = if 0 < c i x then g i d else if c i x < 0 then -(g i d) else |g i d| := by
                  simp [hi_pos, hi_neg, hi_zero]
    have hsum_real :
        (Finset.sum s.attach (fun i ↦ μ i * g i d) : ℝ) ≤
          clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d := by
      calc
        (Finset.sum s.attach (fun i ↦ μ i * g i d) : ℝ)
            ≤ Finset.sum s.attach (fun i ↦
                if 0 < c i x then
                  g i d
                else if c i x < 0 then
                  -(g i d)
                else
                  |g i d|) := by
                  exact Finset.sum_le_sum fun i hi ↦ hscalar i
        _ = clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d := by
              have hsupport_attach :
                  clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d =
                    Finset.sum s.attach (fun i ↦
                      if 0 < c i x then
                        g i d
                      else if c i x < 0 then
                        -(g i d)
                      else
                        |g i d|) := by
                    calc
                      clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d =
                          Finset.sum s (fun i ↦
                            if 0 < c i x then
                              (toDual ℝ E (gradient (c i) x)) d
                            else if c i x < 0 then
                              -((toDual ℝ E (gradient (c i) x)) d)
                            else
                              |(toDual ℝ E (gradient (c i) x)) d|) := by
                            exact clarkeDirectionalDerivReal_absoluteSum_eq_support_sum
                              (s := s) (c := c) (x := x) hC1 d
                      _ = Finset.sum s.attach (fun i ↦
                            if 0 < c i x then
                              g i d
                            else if c i x < 0 then
                              -(g i d)
                            else
                              |g i d|) := by
                            simpa [g] using
                              (Finset.sum_attach (s := s) (f := fun i ↦
                                if 0 < c i x then
                                  (toDual ℝ E (gradient (c i) x)) d
                                else if c i x < 0 then
                                  -((toDual ℝ E (gradient (c i) x)) d)
                                else
                                  |(toDual ℝ E (gradient (c i) x)) d|)).symm
              exact hsupport_attach.symm
    -- Compare the chosen coefficient combination with the exact support identity for the
    -- absolute sum.
    have hsumE :
        (((Finset.sum s.attach (fun i ↦ μ i * g i d) : ℝ)) : EReal) ≤
          (fun y ↦ Finset.sum s (fun i ↦ |c i y|))ᵒ(x; d) := by
      calc
        (((Finset.sum s.attach (fun i ↦ μ i * g i d) : ℝ)) : EReal) ≤
            (((clarkeDirectionalDerivReal (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d : ℝ)) :
              EReal) := by
              exact_mod_cast hsum_real
        _ = (fun y ↦ Finset.sum s (fun i ↦ |c i y|))ᵒ(x; d) := by
              exact coe_clarkeDirectionalDerivReal_of_locallyLipschitzAt
                (fun y ↦ Finset.sum s (fun i ↦ |c i y|)) x d hlocal_sum
    simpa [g, targetStrong, smul_eq_mul] using hsumE

end absoluteSum

#print axioms activeIndices
#print axioms absoluteSumCoefficients
#print axioms locallyLipschitzAt_pointwiseMax_of_contDiffAt
#print axioms locallyLipschitzAt_absoluteSum_of_contDiffAt

end
