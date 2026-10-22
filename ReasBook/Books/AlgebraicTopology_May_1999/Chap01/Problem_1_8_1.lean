/-
Authors: Ze Yuan, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@4885723414c12d37f87f501b8d8b3115b62742f8:README.md (formalization Contributors column).
-/

import Mathlib
import AlgebraicTopology_May_1999.Chap01.ProofStep_1_7_7

-- Declarations for this item will be appended below by the statement pipeline.

noncomputable section

open scoped ContinuousMap CircleDegree

/-- Helper for Problem 1.8.1: the normalized boundary map of a product polynomial is the pointwise
product of the normalized boundary maps of the two factors. -/
-- Proof sketch: evaluate both sides on `S¹`, rewrite polynomial evaluation of a product, and use
-- multiplicativity of `complexDivNormCircle`.
theorem polynomialNormalizedBoundaryMap_mul
    (f g : Polynomial ℂ)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0)
    (hg : ∀ z : Circle, Polynomial.eval (z : ℂ) g ≠ 0) :
    polynomialNormalizedBoundaryMap (f * g)
      (fun z ↦ by
        rw [Polynomial.eval_mul]
        exact mul_ne_zero (hf z) (hg z)) =
      polynomialNormalizedBoundaryMap f hf * polynomialNormalizedBoundaryMap g hg := by
  ext z
  -- Compare the two circle-valued maps pointwise on the boundary.
  rw [polynomialNormalizedBoundaryMap_apply, ContinuousMap.mul_apply,
    polynomialNormalizedBoundaryMap_apply, polynomialNormalizedBoundaryMap_apply]
  simpa [Polynomial.eval_mul] using congrArg (fun w : Circle ↦ (w : ℂ))
    (complexDivNormCircle_mul (Polynomial.eval (z : ℂ) f) (Polynomial.eval (z : ℂ) g) (hf z) (hg z))

/-- Helper for Problem 1.8.1: equal polynomials with boundary nonvanishing define the same
normalized boundary map. -/
-- Proof sketch: compare the two continuous maps pointwise and use proof-irrelevance through
-- `complexDivNormCircle_congr`.
theorem polynomialNormalizedBoundaryMap_congr {f g : Polynomial ℂ}
    (hfg : f = g)
    (hf : ∀ z : Circle, Polynomial.eval (z : ℂ) f ≠ 0)
    (hg : ∀ z : Circle, Polynomial.eval (z : ℂ) g ≠ 0) :
    polynomialNormalizedBoundaryMap f hf = polynomialNormalizedBoundaryMap g hg := by
  subst hfg
  ext z
  simp [polynomialNormalizedBoundaryMap_apply]

/-- Helper for Problem 1.8.1: the normalized boundary map of a nonzero constant polynomial is the
corresponding constant circle-valued map. -/
-- Proof sketch: evaluation of `C a` is constantly `a`, so normalization on the boundary is also
-- constant.
theorem polynomialNormalizedBoundaryMap_C (a : ℂ) (ha : a ≠ 0) :
    polynomialNormalizedBoundaryMap (Polynomial.C a)
      (fun z ↦ by simpa [Polynomial.eval_C] using ha) =
      ContinuousMap.const Circle (complexDivNormCircle a ha) := by
  ext z
  simp [polynomialNormalizedBoundaryMap_apply, Polynomial.eval_C]

/-- Helper for Problem 1.8.1: pointwise multiplication preserves homotopy between circle-valued
continuous maps. -/
-- Proof sketch: choose explicit homotopies for the two factors and multiply their values
-- pointwise in `Circle`.
theorem homotopic_mul {f₀ f₁ g₀ g₁ : C(Circle, Circle)}
    (hf : f₀.Homotopic f₁) (hg : g₀.Homotopic g₁) :
    (f₀ * g₀).Homotopic (f₁ * g₁) := by
  rcases hf with ⟨F⟩
  rcases hg with ⟨G⟩
  refine ⟨{
    toFun := fun x ↦ F x * G x
    continuous_toFun := F.continuous.mul G.continuous
    map_zero_left := ?_
    map_one_left := ?_ }⟩
  · intro z
    -- At time `0`, the product homotopy evaluates to the product of the two initial maps.
    simp
  · intro z
    -- At time `1`, the product homotopy evaluates to the product of the two terminal maps.
    simp

/-- Problem 1.8.1: if a complex polynomial has no root on `S¹`, then the number of its roots in
the open unit disk, counted with multiplicity, equals the degree of the normalized boundary map
`z ↦ p(z) / |p(z)|`. -/
-- Proof sketch: factor `p` according to whether its roots lie inside or outside the open unit
-- disk. The factors coming from roots inside the disk contribute one unit of degree each, using
-- the monic outside-zero computation for normalized boundary maps, while the factors with all
-- roots outside contribute degree `0` by the closed-disk homotopy argument. Additivity of degree
-- under multiplication then gives the desired count.
theorem circleDegree_polynomialNormalizedBoundaryMap_eq_card_roots_inside_open_unit_disk
    (p : Polynomial ℂ)
    (hp : ∀ z : Circle, p.eval (z : ℂ) ≠ 0) :
    deg(polynomialNormalizedBoundaryMap p hp) =
      ((p.roots.filter fun z ↦ ‖z‖ < 1).card : ℤ) := by
  let sIn : Multiset ℂ := p.roots.filter fun z ↦ ‖z‖ < 1
  let sOut : Multiset ℂ := p.roots.filter fun z ↦ ¬ ‖z‖ < 1
  let pin : Polynomial ℂ := (sIn.map fun a ↦ Polynomial.X - Polynomial.C a).prod
  let pout : Polynomial ℂ := (sOut.map fun a ↦ Polynomial.X - Polynomial.C a).prod
  let q : Polynomial ℂ := pin * pout
  have hp_eval_one : Polynomial.eval (1 : ℂ) p ≠ 0 := by
    -- Evaluating on the circle at `1` rules out the zero polynomial.
    simpa using hp 1
  have hpnz : p ≠ 0 := by
    intro hpz
    simp [hpz] at hp_eval_one
  have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hpnz
  have hsplitRoots : sIn + sOut = p.roots := by
    -- The root multiset partitions into roots inside the open disk and its complement.
    simpa [sIn, sOut] using
      (Multiset.filter_add_not (p := fun z : ℂ ↦ ‖z‖ < 1) p.roots)
  have hroots : p.roots.card = p.natDegree := by
    -- Over `ℂ`, every polynomial splits, so the root multiset has full cardinality.
    simpa using (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  have hpinMonic : pin.Monic := by
    -- Each factor `X - a` is monic, so their multiset product is monic.
    dsimp [pin]
    exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hpoutMonic : pout.Monic := by
    -- The complementary root factor is also monic for the same reason.
    dsimp [pout]
    exact Polynomial.monic_multiset_prod_of_monic _ _ fun a _ ↦ Polynomial.monic_X_sub_C a
  have hpinnz : pin ≠ 0 := hpinMonic.ne_zero
  have hpoutnz : pout ≠ 0 := hpoutMonic.ne_zero
  have hpinOutside : ∀ z : ℂ, 1 ≤ ‖z‖ → Polynomial.eval z pin ≠ 0 := by
    intro z hzNorm hzEval
    have hz_mem_pin : z ∈ pin.roots := by
      rwa [Polynomial.mem_roots hpinnz]
    have hz_mem_in : z ∈ sIn := by
      simpa [pin] using (Polynomial.roots_multiset_prod_X_sub_C sIn ▸ hz_mem_pin)
    have hz_lt : ‖z‖ < 1 := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ‖w‖ < 1) := by
        simpa [sIn] using hz_mem_in
      exact (Multiset.mem_filter.1 hz_filter).2
    exact (not_lt_of_ge hzNorm) hz_lt
  have hpoutClosed : ∀ z : ℂ, z ∈ Metric.closedBall (0 : ℂ) 1 → Polynomial.eval z pout ≠ 0 := by
    intro z hzBall hzEval
    have hz_mem_pout : z ∈ pout.roots := by
      exact (Polynomial.mem_roots hpoutnz).2 (by simpa [Polynomial.IsRoot] using hzEval)
    have hz_mem_out : z ∈ sOut := by
      simpa [pout] using (Polynomial.roots_multiset_prod_X_sub_C sOut ▸ hz_mem_pout)
    have hz_not_lt : ¬ ‖z‖ < 1 := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ¬ ‖w‖ < 1) := by
        simpa [sOut] using hz_mem_out
      exact (Multiset.mem_filter.1 hz_filter).2
    have hz_le : ‖z‖ ≤ 1 := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hzBall
    have hz_norm : ‖z‖ = 1 := le_antisymm hz_le (not_lt.mp hz_not_lt)
    let w : Circle := ⟨z, mem_sphere_zero_iff_norm.2 hz_norm⟩
    have hz_mem_p : z ∈ p.roots := by
      have hz_filter : z ∈ p.roots.filter (fun w : ℂ ↦ ¬ ‖w‖ < 1) := by
        simpa [sOut] using hz_mem_out
      exact (Multiset.mem_filter.1 hz_filter).1
    have hpz : Polynomial.eval z p = 0 := by
      exact (Polynomial.mem_roots hpnz).1 hz_mem_p
    have hpw : Polynomial.eval (w : ℂ) p ≠ 0 := hp w
    exact hpw (by simpa [w] using hpz)
  have hpinCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) pin ≠ 0 :=
    polynomial_eval_ne_zero_on_circle_of_no_root_outside_open_unit_disk pin hpinOutside
  have hpoutCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) pout ≠ 0 :=
    polynomial_eval_ne_zero_on_circle_of_nonvanishing_closed_unit_disk pout hpoutClosed
  have hfactor : Polynomial.C p.leadingCoeff * q = p := by
    -- Rewrite `p` as its leading coefficient times the product over the inside/outside root split.
    have hrootProd :
        (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod = q := by
      calc
        (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod =
            (((sIn + sOut).map fun a ↦ Polynomial.X - Polynomial.C a).prod) := by
              rw [← hsplitRoots]
        _ = (sIn.map fun a ↦ Polynomial.X - Polynomial.C a).prod *
              (sOut.map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
              rw [Multiset.map_add, Multiset.prod_add]
        _ = q := by
              rfl
    calc
      Polynomial.C p.leadingCoeff * q =
          Polynomial.C p.leadingCoeff * (p.roots.map fun a ↦ Polynomial.X - Polynomial.C a).prod := by
            rw [hrootProd]
      _ = p := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C (p := p) hroots
  have hqCircle : ∀ z : Circle, Polynomial.eval (z : ℂ) q ≠ 0 := by
    intro z
    -- The product factor is nonzero on `S¹` because both subfactors are.
    dsimp [q]
    rw [Polynomial.eval_mul]
    exact mul_ne_zero (hpinCircle z) (hpoutCircle z)
  have hq_mul_C : q * Polynomial.C p.leadingCoeff = p := by
    -- Move the constant leading-coefficient factor to the right for the boundary-map lemma.
    calc
      q * Polynomial.C p.leadingCoeff = Polynomial.C p.leadingCoeff * q := by
        rw [mul_comm]
      _ = p := hfactor
  have hconstCompare :
      (polynomialNormalizedBoundaryMap p hp).Homotopic
        (polynomialNormalizedBoundaryMap q hqCircle) := by
    have hqCircleMul : ∀ z : Circle, Polynomial.eval (z : ℂ) (q * Polynomial.C p.leadingCoeff) ≠ 0 := by
      intro z
      rw [Polynomial.eval_mul, Polynomial.eval_C]
      exact mul_ne_zero (hqCircle z) hlead
    have hp_eq :
        polynomialNormalizedBoundaryMap p hp =
          polynomialNormalizedBoundaryMap (q * Polynomial.C p.leadingCoeff) hqCircleMul := by
      symm
      exact polynomialNormalizedBoundaryMap_congr hq_mul_C hqCircleMul hp
    have hleadConst :
        (ContinuousMap.const Circle (complexDivNormCircle p.leadingCoeff hlead)).Homotopic
          (1 : C(Circle, Circle)) := by
      -- The leading coefficient contributes only a constant phase on the boundary.
      rw [show (1 : C(Circle, Circle)) = ContinuousMap.const Circle (1 : Circle) by rfl]
      simpa using
        (ContinuousMap.homotopic_const_iff).2
          (PathConnectedSpace.joined (complexDivNormCircle p.leadingCoeff hlead) 1)
    -- Route correction: instead of proving degree additivity directly, first strip the nonzero
    -- constant factor by splitting off the constant polynomial `C(p.leadingCoeff)`.
    rw [hp_eq]
    rw [polynomialNormalizedBoundaryMap_mul q (Polynomial.C p.leadingCoeff) hqCircle
      (fun z ↦ by simpa [Polynomial.eval_C] using hlead)]
    rw [polynomialNormalizedBoundaryMap_C]
    simpa using
      homotopic_mul
        (ContinuousMap.Homotopic.refl (polynomialNormalizedBoundaryMap q hqCircle))
        hleadConst
  have hpinHom :
      (polynomialNormalizedBoundaryMap pin hpinCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    -- The inside-root factor contributes one degree for each root inside the open disk.
    simpa [pin] using
      polynomialNormalizedBoundaryMap_homotopic_id_zpow_of_monic_of_no_root_outside_open_unit_disk
        pin hpinOutside hpinMonic
  let cOut : Circle :=
    complexDivNormCircle (Polynomial.eval (0 : ℂ) pout)
      (polynomial_eval_zero_ne_zero_of_nonvanishing_closed_unit_disk pout hpoutClosed)
  have hpoutHom :
      (polynomialNormalizedBoundaryMap pout hpoutCircle).Homotopic
        (ContinuousMap.const Circle cOut) := by
    -- The complementary factor has no zeros on the closed disk, so its boundary map contracts to
    -- a constant.
    simpa [cOut, hpoutCircle] using
      polynomialNormalizedBoundaryMap_homotopic_const_of_no_root_closed_unit_disk pout hpoutClosed
  have hconstOut :
      (ContinuousMap.const Circle cOut).Homotopic (1 : C(Circle, Circle)) := by
    -- Any constant map on `S¹` is homotopic to the constant map at `1`.
    rw [show (1 : C(Circle, Circle)) = ContinuousMap.const Circle (1 : Circle) by rfl]
    simpa using (ContinuousMap.homotopic_const_iff).2 (PathConnectedSpace.joined cOut 1)
  have hqHom :
      (polynomialNormalizedBoundaryMap q hqCircle).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    have hmul :
        (polynomialNormalizedBoundaryMap q hqCircle).Homotopic
          (((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) * ContinuousMap.const Circle cOut) := by
      -- Factor the boundary map of `q = pin * pout` and combine the two imported homotopies.
      dsimp [q]
      rw [polynomialNormalizedBoundaryMap_mul pin pout hpinCircle hpoutCircle]
      exact homotopic_mul hpinHom hpoutHom
    refine ContinuousMap.Homotopic.trans hmul ?_
    -- Finally remove the constant factor on the right.
    simpa [mul_one] using
      homotopic_mul
        (ContinuousMap.Homotopic.refl ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)))
        hconstOut
  have hfinal :
      (polynomialNormalizedBoundaryMap p hp).Homotopic
        ((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) := by
    -- Concatenate the leading-coefficient reduction with the inside/outside factor homotopy.
    exact ContinuousMap.Homotopic.trans hconstCompare hqHom
  calc
    deg(polynomialNormalizedBoundaryMap p hp) =
        deg((ContinuousMap.id Circle) ^ (sIn.card : ℤ)) :=
      circleDegree_eq_of_homotopic _ _ hfinal
    _ = (sIn.card : ℤ) := circleDegree_id_zpow _
    _ = ((p.roots.filter fun z ↦ ‖z‖ < 1).card : ℤ) := by
      simp [sIn]
