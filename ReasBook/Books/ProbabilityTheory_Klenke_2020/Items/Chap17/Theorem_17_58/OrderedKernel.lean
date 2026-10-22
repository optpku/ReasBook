/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Mathlib

open scoped BigOperators

noncomputable section

namespace ProbabilityTheory

variable {α : Type*} [Fintype α] [PartialOrder α]

/-- Helper for Theorem 17.58: `orderedRowKernelSet` is the raw ambient polytope of row-stochastic
kernels whose off-order entries vanish. -/
def orderedRowKernelSet : Set (α → α → ℝ) :=
  {K | (∀ a, K a ∈ stdSimplex ℝ α) ∧ ∀ a b, ¬ a ≤ b → K a b = 0}

/-- Helper for Theorem 17.58: the ordered second marginal of a raw kernel with first marginal
weights `p`. -/
def orderedSecondMarginalMap (p : α → ℝ) (K : α → α → ℝ) : α → ℝ :=
  fun b ↦ ∑ a, p a * K a b

/-- Helper for Theorem 17.58: the attainable second marginals coming from ordered raw kernels. -/
def orderedSecondMarginalSet (p : α → ℝ) : Set (α → ℝ) :=
  orderedSecondMarginalMap p '' orderedRowKernelSet (α := α)

/-- Helper for Theorem 17.58: membership in `orderedRowKernelSet` records row-simplex conditions
rowwise. -/
lemma mem_stdSimplex_of_mem_orderedRowKernelSet {K : α → α → ℝ}
    (hK : K ∈ orderedRowKernelSet (α := α)) (a : α) :
    K a ∈ stdSimplex ℝ α :=
  hK.1 a

/-- Helper for Theorem 17.58: membership in `orderedRowKernelSet` kills entries away from the order
relation. -/
lemma eq_zero_of_mem_orderedRowKernelSet {K : α → α → ℝ}
    (hK : K ∈ orderedRowKernelSet (α := α)) {a b : α} (hab : ¬ a ≤ b) :
    K a b = 0 :=
  hK.2 a b hab

/-- Helper for Theorem 17.58: `orderedSecondMarginalMap` is additive in the kernel variable. -/
lemma orderedSecondMarginalMap_add (p : α → ℝ) (K L : α → α → ℝ) :
    orderedSecondMarginalMap p (K + L) =
      orderedSecondMarginalMap p K + orderedSecondMarginalMap p L := by
  -- Proof comment: expand the second marginal coordinatewise and distribute the finite sum over
  -- rowwise addition.
  ext b
  simp [orderedSecondMarginalMap, mul_add, Finset.sum_add_distrib]

/-- Helper for Theorem 17.58: `orderedSecondMarginalMap` is linear in the kernel variable. -/
lemma orderedSecondMarginalMap_smul (p : α → ℝ) (c : ℝ) (K : α → α → ℝ) :
    orderedSecondMarginalMap p (c • K) =
      c • orderedSecondMarginalMap p K := by
  -- Proof comment: pull the scalar through each row contribution and then through the finite sum.
  ext b
  calc
    orderedSecondMarginalMap p (c • K) b = ∑ a, c * (p a * K a b) := by
      simp [orderedSecondMarginalMap, mul_left_comm]
    _ = c * ∑ a, p a * K a b := by
      rw [Finset.mul_sum]
    _ = (c • orderedSecondMarginalMap p K) b := by
      simp [orderedSecondMarginalMap]

/-- Helper for Theorem 17.58: the second-marginal construction is a linear map on raw kernels. -/
def orderedSecondMarginalLinearMap (p : α → ℝ) :
    (α → α → ℝ) →ₗ[ℝ] α → ℝ where
  toFun := orderedSecondMarginalMap p
  map_add' := orderedSecondMarginalMap_add p
  map_smul' := orderedSecondMarginalMap_smul p

/-- Helper for Theorem 17.58: the raw ordered-kernel polytope is convex in ambient coordinates. -/
lemma convex_orderedRowKernelSet :
    Convex ℝ (orderedRowKernelSet (α := α)) := by
  intro K hK L hL s t hs ht hst
  refine ⟨?_, ?_⟩
  · -- Proof comment: each row stays in the simplex because the simplex is convex.
    intro a
    exact (convex_stdSimplex (𝕜 := ℝ) (ι := α)) (hK.1 a) (hL.1 a) hs ht hst
  · -- Proof comment: the off-order coordinates remain zero under convex combinations.
    intro a b hab
    simp [Pi.add_apply, Pi.smul_apply, hK.2 a b hab, hL.2 a b hab]

/-- Helper for Theorem 17.58: the attainable second marginals form a convex set because they are
the linear image of the raw ordered-kernel polytope. -/
lemma convex_orderedSecondMarginalSet (p : α → ℝ) :
    Convex ℝ (orderedSecondMarginalSet (α := α) p) := by
  -- Proof comment: after fixing the ambient linear map, convexity is inherited from the source
  -- ordered-kernel polytope.
  simpa [orderedSecondMarginalSet] using
    (convex_orderedRowKernelSet (α := α)).linear_image (orderedSecondMarginalLinearMap p)

/-- Helper for Theorem 17.58: the raw ordered-kernel polytope is closed in the ambient finite
coordinate space. -/
lemma orderedRowKernelSet_isClosed :
    IsClosed (orderedRowKernelSet (α := α)) := by
  classical
  let rowSet : Set (α → α → ℝ) := Set.pi Set.univ (fun _ : α ↦ stdSimplex ℝ α)
  have hRows : IsClosed rowSet := by
    exact isClosed_set_pi fun _ _ ↦ isClosed_stdSimplex ℝ α
  have hOff :
      IsClosed (⋂ a : α, ⋂ b : α, {K : α → α → ℝ | ¬ a ≤ b → K a b = 0}) := by
    refine isClosed_iInter fun a ↦ ?_
    refine isClosed_iInter fun b ↦ ?_
    by_cases hab : a ≤ b
    · -- Proof comment: ordered coordinates impose no constraint, so this slice is all of space.
      simp [hab]
    · -- Proof comment: off-order coordinates are cut out by one continuous evaluation equation.
      simpa [hab] using
        (isClosed_eq ((continuous_apply b).comp (continuous_apply a)) continuous_const)
  have hEq :
      orderedRowKernelSet (α := α) =
        rowSet ∩ ⋂ a : α, ⋂ b : α, {K : α → α → ℝ | ¬ a ≤ b → K a b = 0} := by
    ext K
    simp [orderedRowKernelSet, rowSet, Set.mem_pi]
  rw [hEq]
  exact hRows.inter hOff

/-- Helper for Theorem 17.58: the raw ordered-kernel polytope is compact because each row lies in
the standard simplex and the off-order support equations are closed. -/
lemma orderedRowKernelSet_isCompact :
    IsCompact (orderedRowKernelSet (α := α)) := by
  let rowSet : Set (α → α → ℝ) := Set.pi Set.univ (fun _ : α ↦ stdSimplex ℝ α)
  have hRowsCompact : IsCompact rowSet := by
    simpa [rowSet] using isCompact_univ_pi (fun _ : α ↦ isCompact_stdSimplex ℝ α)
  have hSubset : orderedRowKernelSet (α := α) ⊆ rowSet := by
    intro K hK
    simpa [rowSet, Set.mem_pi] using hK.1
  exact IsCompact.of_isClosed_subset hRowsCompact
    (orderedRowKernelSet_isClosed (α := α)) hSubset

/-- Helper for Theorem 17.58: the attainable ordered second marginals form a compact set because
they are the image of the compact raw kernel polytope under a linear map. -/
lemma orderedSecondMarginalSet_isCompact (p : α → ℝ) :
    IsCompact (orderedSecondMarginalSet (α := α) p) := by
  -- Proof comment: in the finite-dimensional ambient space every linear map is continuous, so the
  -- image of the compact source polytope is compact.
  simpa [orderedSecondMarginalSet] using
    (orderedRowKernelSet_isCompact (α := α)).image
      ((orderedSecondMarginalLinearMap p).continuous_of_finiteDimensional)

/-- Helper for Theorem 17.58: a deterministic selector `σ` produces an extreme ordered kernel. -/
def deterministicOrderedKernel (σ : α → α) : α → α → ℝ :=
  by
    classical
    exact fun a b ↦ if b = σ a then 1 else 0

/-- Helper for Theorem 17.58: deterministic ordered kernels lie in `orderedRowKernelSet` provided
the selector only moves points upward. -/
lemma deterministicOrderedKernel_mem_orderedRowKernelSet (σ : α → α)
    (hσ : ∀ a, a ≤ σ a) :
    deterministicOrderedKernel σ ∈ orderedRowKernelSet (α := α) := by
  classical
  refine ⟨?_, ?_⟩
  · -- Proof comment: each deterministic row is exactly a simplex vertex.
    intro a
    simpa [deterministicOrderedKernel, eq_comm] using
      (ite_eq_mem_stdSimplex (𝕜 := ℝ) (ι := α) (i := σ a))
  · -- Proof comment: if `b` is not above `a`, then the deterministic selector cannot land at `b`.
    intro a b hab
    by_cases hEq : b = σ a
    · exact (hab (hEq ▸ hσ a)).elim
    · simp [deterministicOrderedKernel, hEq]

/-- Helper for Theorem 17.58: a continuous linear functional on a finite coordinate space expands
against the standard basis vectors written in `if`-form. -/
lemma strongDual_apply_eq_sum_single [DecidableEq α]
    (l : StrongDual ℝ (α → ℝ)) (x : α → ℝ) :
    l x = ∑ b, x b * l (fun j ↦ if b = j then 1 else 0) := by
  -- Proof comment: this is the finite-coordinate expansion of a linear functional in the standard
  -- basis, restated using `Pi.single`.
  simpa [smul_eq_mul] using l.toLinearMap.pi_apply_eq_sum_univ x

/-- Helper for Theorem 17.58: monotone test inequalities force the target vector to lie in the
compact convex image of ordered raw kernels. -/
lemma existsOrderedRowKernel_of_monotoneLE
    (p q : α → ℝ)
    (hq_nonneg : ∀ b, 0 ≤ q b)
    (hMono : ∀ {g : α → ℝ}, Monotone g →
      ∑ a, p a * g a ≤ ∑ b, q b * g b) :
    ∃ K ∈ orderedRowKernelSet (α := α), orderedSecondMarginalMap p K = q := by
  classical
  have hq_mem :
      q ∈ orderedSecondMarginalSet (α := α) p := by
    rw [← iInter_halfSpaces_eq
      (s := orderedSecondMarginalSet (α := α) p)
      (hs₁ := convex_orderedSecondMarginalSet (α := α) p)
      (hs₂ := (orderedSecondMarginalSet_isCompact (α := α) p).isClosed)]
    simp only [Set.mem_iInter, Set.mem_setOf_eq]
    intro l
    let coeff : α → ℝ := fun b ↦ l (fun j ↦ if b = j then 1 else 0)
    let upperClosure : α → Finset α := fun a ↦ Finset.univ.filter fun b ↦ a ≤ b
    have hUpper_nonempty : ∀ a, (upperClosure a).Nonempty := by
      intro a
      exact ⟨a, by simp [upperClosure]⟩
    let σ : α → α := fun a ↦
      Classical.choose (Finset.exists_max_image (upperClosure a) coeff (hUpper_nonempty a))
    have hσ_mem : ∀ a, σ a ∈ upperClosure a := by
      intro a
      exact
        (Classical.choose_spec
          (Finset.exists_max_image (upperClosure a) coeff (hUpper_nonempty a))).1
    have hσ_max : ∀ a {c}, c ∈ upperClosure a → coeff c ≤ coeff (σ a) := by
      intro a c hc
      exact
        (Classical.choose_spec
          (Finset.exists_max_image (upperClosure a) coeff (hUpper_nonempty a))).2 c hc
    have hσ_mono : ∀ a, a ≤ σ a := by
      intro a
      exact (Finset.mem_filter.mp (hσ_mem a)).2
    let env : α → ℝ := fun a ↦ coeff (σ a)
    have hCoeff_le_env : ∀ b, coeff b ≤ env b := by
      intro b
      exact hσ_max b (by simp [upperClosure])
    have hEnv_antitone : Antitone env := by
      intro a b hab
      exact hσ_max a
        (by
          refine Finset.mem_filter.mpr ?_
          exact ⟨Finset.mem_univ _, le_trans hab (hσ_mono b)⟩)
    have hNegEnv_mono : Monotone fun a ↦ -env a := by
      intro a b hab
      exact neg_le_neg (hEnv_antitone hab)
    have hEnv_compare :
        ∑ b, q b * env b ≤ ∑ a, p a * env a := by
      -- Proof comment: apply the monotone test inequality to the increasing function `-env`.
      have hNeg :=
        hMono (g := fun a ↦ -env a) hNegEnv_mono
      have hNeg' : -(∑ a, p a * env a) ≤ -(∑ b, q b * env b) := by
        simpa [Finset.sum_neg_distrib, mul_comm, mul_left_comm, mul_assoc] using hNeg
      exact neg_le_neg_iff.mp hNeg'
    let K := deterministicOrderedKernel σ
    have hK : K ∈ orderedRowKernelSet (α := α) := by
      -- Proof comment: the selector `σ` always moves mass upward, so the deterministic kernel is
      -- supported on the order relation.
      exact deterministicOrderedKernel_mem_orderedRowKernelSet σ hσ_mono
    have hKernel_eval :
        l (orderedSecondMarginalMap p K) = ∑ a, p a * env a := by
      -- Proof comment: expanding the linear functional in the standard basis turns the
      -- deterministic kernel into the chosen envelope values.
      calc
        l (orderedSecondMarginalMap p K) =
            ∑ b, orderedSecondMarginalMap p K b * coeff b := by
              simpa [coeff] using
                strongDual_apply_eq_sum_single (l := l) (x := orderedSecondMarginalMap p K)
        _ = ∑ b, (∑ a, p a * K a b) * coeff b := by
              simp [orderedSecondMarginalMap]
        _ = ∑ b, ∑ a, p a * (K a b * coeff b) := by
              refine Finset.sum_congr rfl ?_
              intro b hb
              rw [Finset.sum_mul]
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
        _ = ∑ a, ∑ b, p a * (K a b * coeff b) := by
              rw [Finset.sum_comm]
        _ = ∑ a, p a * ∑ b, K a b * coeff b := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rw [← Finset.mul_sum]
        _ = ∑ a, p a * env a := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              simp [K, deterministicOrderedKernel, env]
    have hq_eval :
        l q = ∑ b, q b * coeff b := by
      -- Proof comment: the same coordinate expansion computes the dual pairing with `q`.
      simpa [coeff] using strongDual_apply_eq_sum_single (l := l) (x := q)
    refine ⟨orderedSecondMarginalMap p K, ⟨K, hK, rfl⟩, ?_⟩
    calc
      l q = ∑ b, q b * coeff b := hq_eval
      _ ≤ ∑ b, q b * env b := by
            refine Finset.sum_le_sum ?_
            intro b hb
            simpa [env, mul_comm, mul_left_comm, mul_assoc] using
              mul_le_mul_of_nonneg_left (hCoeff_le_env b) (hq_nonneg b)
      _ ≤ ∑ a, p a * env a := hEnv_compare
      _ = l (orderedSecondMarginalMap p K) := hKernel_eval.symm
  simpa [orderedSecondMarginalSet] using hq_mem

end ProbabilityTheory
