import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

/-!
Theorem 3.40 lies in finite-dimensional convex geometry.

Domain-style sampling for this refine pass:
* core/canonical owner: `PointedCone.hull`
* canonical membership API: `PointedCone.mem_hull_set`
* nearby project owner precedent: Chapter 3's generated-cone files now treat source-facing cone
  presentations as bridges to canonical cone owners rather than as second root definitions

Primitive data vs. derived API:
* primitive source-facing witness data here: a finite family `r : Fin q → E` with coefficients
  `coeff : Fin q → 𝕜`
* derived/canonical ambient owner: membership of `v` in `PointedCone.hull 𝕜 X`

Accordingly, this file keeps the finite-family presentation only as a bridge theorem and states the
main result over the canonical owner `PointedCone.hull`.
-/

open scoped BigOperators

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E]

/-- Bridge/view: membership in `PointedCone.hull 𝕜 X` unfolds to a finite nonnegative linear-
combination presentation using vectors from `X`. -/
theorem mem_hull_iff {X : Set E} {v : E} :
    v ∈ PointedCone.hull 𝕜 X ↔
      ∃ q : ℕ, ∃ r : Fin q → E, (∀ j, r j ∈ X) ∧
        ∃ coeff : Fin q → 𝕜, (∀ j, 0 ≤ coeff j) ∧ v = ∑ j, coeff j • r j := by
  constructor
  · intro hv
    -- Reindex the finitely-supported cone witness by `Fin`.
    rw [PointedCone.mem_hull_set] at hv
    obtain ⟨c, hcX, hcoeff, hsum⟩ := hv
    classical
    let A : c.support ≃ Fin c.support.card := Finset.equivFin c.support
    have hsum' : ∑ x : c.support, c x • (x : E) = v := by
      have hsum'' : ∑ x ∈ c.support, c x • x = v := by
        simpa [Finsupp.sum] using hsum
      rw [← Finset.sum_attach] at hsum''
      exact hsum''
    refine ⟨c.support.card, fun j => (A.symm j : E), ?_⟩
    constructor
    · intro j
      exact hcX (A.symm j).property
    · refine ⟨fun j => c (A.symm j), ?_⟩
      constructor
      · intro j
        exact hcoeff _
      · calc
          v = ∑ x : c.support, c x • (x : E) := hsum'.symm
          _ = ∑ j : Fin c.support.card, c (A.symm j) • ((A.symm j : c.support) : E) := by
            exact
              (Fintype.sum_equiv A.symm _ (fun x : c.support => c x • (x : E))
                (fun i => rfl)).symm
  · rintro ⟨q, r, hrX, coeff, hcoeff, rfl⟩
    classical
    let cfin : Fin q →₀ 𝕜 := Finsupp.equivFunOnFinite.symm coeff
    let c : E →₀ 𝕜 := Finsupp.mapDomain r cfin
    -- Package the finite family back into a finitely-supported cone witness.
    rw [PointedCone.mem_hull_set]
    refine ⟨c, ?_, ?_, ?_⟩
    · intro x hx
      by_contra hxX
      have hxrange : x ∉ Set.range r := by
        rintro ⟨j, rfl⟩
        exact hxX (hrX j)
      have hzero : c x = 0 := by
        simpa [c] using Finsupp.mapDomain_notin_range cfin x hxrange
      exact (Finsupp.mem_support_iff.mp hx) hzero
    · intro x
      by_cases hx : x ∈ Set.range r
      · rcases hx with ⟨j, rfl⟩
        rw [show c (r j) = (cfin.mapDomain r) (r j) by rfl, Finsupp.mapDomain_apply_eq_sum]
        refine Finset.sum_nonneg ?_
        intro i hi
        simpa [cfin] using hcoeff i
      · have hzero : c x = 0 := by
          simpa [c] using Finsupp.mapDomain_notin_range cfin x hx
        simpa [hzero]
    · calc
        c.sum (fun x a => a • x) = cfin.sum (fun j a => a • r j) := by
          simpa [c, Finsupp.linearCombination] using
            (Finsupp.linearCombination_mapDomain (R := 𝕜) (v' := fun x : E => x) r cfin)
        _ = ∑ j, coeff j • r j := by
          simpa [cfin] using
            (Finsupp.sum_fintype cfin (fun j a => a • r j) fun i => zero_smul 𝕜 (r i))

/-- Helper for Theorem 3.40: hull membership over a finite set can be expressed with
subtype-indexed nonnegative coefficients. -/
lemma exists_nonnegCoeff_sum_subtype_of_mem_hull_finset [DecidableEq E] {t : Finset E} {x : E}
    (hx : x ∈ PointedCone.hull 𝕜 (↑t : Set E)) :
    ∃ coeff : t → 𝕜, (∀ i, 0 ≤ coeff i) ∧ x = ∑ i : t, coeff i • (i : E) := by
  rw [PointedCone.mem_hull_set] at hx
  obtain ⟨c, hc, hcoeff, hsum⟩ := hx
  have hcoeff_support : ∀ y, c y ≠ 0 → y ∈ t := by
    intro y hy
    exact hc (Finsupp.mem_support_iff.mpr hy)
  let d : E →₀ 𝕜 := Finsupp.onFinset t (fun y ↦ c y) hcoeff_support
  have hd : d = c := by
    ext y
    simp [d]
  have hsum_on_t : d.sum (fun y a ↦ a • y) = Finset.sum t (fun y ↦ c y • y) := by
    -- Replace the finitely-supported sum by the original `Finset` sum on `t`.
    simpa [d] using
      (Finsupp.onFinset_sum (f := fun y ↦ c y) (hf := hcoeff_support)
        (g := fun y a ↦ a • y) fun y ↦ zero_smul 𝕜 y)
  refine ⟨fun i ↦ d i, ?_, ?_⟩
  · intro i
    simpa [hd] using hcoeff i
  · -- Rewrite the original `Finsupp` witness onto the subtype-indexed family.
    calc
      x = d.sum (fun y a ↦ a • y) := by simpa [hd] using hsum.symm
      _ = Finset.sum t (fun y ↦ c y • y) := hsum_on_t
      _ = ∑ i : t, c i • (i : E) := by
        simpa using (Finset.sum_coe_sort t (fun y ↦ c y • y)).symm

/-- Helper for Theorem 3.40: a subtype-indexed nonnegative coefficient formula gives hull
membership for the underlying finite set. -/
lemma mem_hull_finset_of_nonnegCoeff_sum_subtype [DecidableEq E] {t : Finset E} {x : E}
    (coeff : t → 𝕜) (hcoeff : ∀ i, 0 ≤ coeff i) (hx : x = ∑ i : t, coeff i • (i : E)) :
    x ∈ PointedCone.hull 𝕜 (↑t : Set E) := by
  have hcoeff_support :
      ∀ y, (if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) ≠ 0 → y ∈ t := by
    intro y hy
    by_cases hyt : y ∈ t
    · exact hyt
    · simp [hyt] at hy
  let c : E →₀ 𝕜 :=
    Finsupp.onFinset t (fun y ↦ if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) hcoeff_support
  have hsupport : c.support ⊆ t := by
    simpa [c] using
      (Finsupp.support_onFinset_subset (s := t)
        (f := fun y ↦ if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) (hf := hcoeff_support))
  have hsum_on_t :
      c.sum (fun y a ↦ a • y) =
        Finset.sum t (fun y ↦ (if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) • y) := by
    -- Expand the `onFinset` witness back to a sum over the ambient finite set.
    simpa [c] using
      (Finsupp.onFinset_sum
        (f := fun y ↦ if hy : y ∈ t then coeff ⟨y, hy⟩ else 0)
        (hf := hcoeff_support) (g := fun y a ↦ a • y) fun y ↦ zero_smul 𝕜 y)
  rw [PointedCone.mem_hull_set]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro y hy
    exact hsupport hy
  · intro y
    by_cases hyt : y ∈ t
    · simpa [c, hyt] using hcoeff ⟨y, hyt⟩
    · have hc_zero : c y = 0 := by
        simp [c, hyt]
      simpa [hc_zero]
  · calc
      c.sum (fun y a ↦ a • y) =
          Finset.sum t (fun y ↦ (if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) • y) := hsum_on_t
      _ = ∑ i : t, coeff i • (i : E) := by
        simpa using (Finset.sum_coe_sort t (fun y ↦ (if hy : y ∈ t then coeff ⟨y, hy⟩ else 0) • y)).symm
      _ = x := hx.symm

/-- Helper for Theorem 3.40: a conic combination supported on a linearly dependent finite set can
be rewritten after erasing one generator. -/
lemma mem_hull_finset_erase_of_not_linearIndependent [DecidableEq E] {t : Finset E}
    (ht : ¬ LinearIndependent 𝕜 (fun x : t => (x : E))) {x : E}
    (hx : x ∈ PointedCone.hull 𝕜 (↑t : Set E)) :
    ∃ y : t, x ∈ PointedCone.hull 𝕜 (↑(t.erase y) : Set E) := by
  obtain ⟨coeff, hcoeff_nonneg, hcoeff_sum⟩ :=
    exists_nonnegCoeff_sum_subtype_of_mem_hull_finset (t := t) hx
  obtain ⟨μ₀, hμ₀sum, i, hμ₀ne⟩ := (Fintype.not_linearIndependent_iff).mp ht
  obtain ⟨μ, hμsum, hμpos⟩ :
      ∃ μ : t → 𝕜, (∑ j, μ j • (j : E)) = 0 ∧ ∃ j, 0 < μ j := by
    rcases lt_or_gt_of_ne hμ₀ne with hi_neg | hi_pos
    · refine ⟨fun j ↦ -μ₀ j, ?_, ?_⟩
      · simpa [neg_smul] using congrArg Neg.neg hμ₀sum
      · exact ⟨i, by simpa using neg_pos.mpr hi_neg⟩
    · exact ⟨μ₀, hμ₀sum, i, hi_pos⟩
  let s : Finset t := Finset.univ.filter (fun j ↦ 0 < μ j)
  obtain ⟨i₀, hi₀s, hmin⟩ : ∃ i₀ ∈ s, ∀ j ∈ s, coeff i₀ / μ i₀ ≤ coeff j / μ j := by
    apply s.exists_min_image fun j ↦ coeff j / μ j
    obtain ⟨j, hj⟩ := hμpos
    exact ⟨j, by simp [s, hj]⟩
  have hμi₀_pos : 0 < μ i₀ := by
    simpa [s] using hi₀s
  let θ : 𝕜 := coeff i₀ / μ i₀
  let k : t → 𝕜 := fun j ↦ coeff j - θ * μ j
  have hθ_nonneg : 0 ≤ θ := by
    -- The minimizing ratio is nonnegative because both numerator and denominator are.
    exact div_nonneg (hcoeff_nonneg i₀) (le_of_lt hμi₀_pos)
  have hk_nonneg : ∀ j, 0 ≤ k j := by
    intro j
    by_cases hj_pos : 0 < μ j
    · have hj_in_s : j ∈ s := by simp [s, hj_pos]
      have hratio : θ ≤ coeff j / μ j := by
        simpa [θ] using hmin j hj_in_s
      have hmul : θ * μ j ≤ coeff j := by
        exact (le_div_iff₀ hj_pos).mp hratio
      exact sub_nonneg.mpr hmul
    · have hμj_nonpos : μ j ≤ 0 := le_of_not_gt hj_pos
      have hmul_nonpos : θ * μ j ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ_nonneg hμj_nonpos
      exact sub_nonneg.mpr (le_trans hmul_nonpos (hcoeff_nonneg j))
  have hk_i₀ : k i₀ = 0 := by
    have hμi₀_ne : μ i₀ ≠ 0 := ne_of_gt hμi₀_pos
    have hθ_mul : θ * μ i₀ = coeff i₀ := by
      calc
        θ * μ i₀ = coeff i₀ / μ i₀ * μ i₀ := rfl
        _ = coeff i₀ := by field_simp [hμi₀_ne]
    simp [k, hθ_mul]
  have hk_sum : x = ∑ j : t, k j • (j : E) := by
    have hscaled_relation : θ • (∑ j : t, μ j • (j : E)) = ∑ j : t, (θ * μ j) • (j : E) := by
      rw [Finset.smul_sum]
      refine Finset.sum_congr rfl ?_
      intro j hj
      rw [smul_smul]
    have hk_decomp :
        ∑ j : t, coeff j • (j : E) =
          ∑ j : t, k j • (j : E) + θ • ∑ j : t, μ j • (j : E) := by
      calc
        ∑ j : t, coeff j • (j : E) = ∑ j : t, (k j + θ * μ j) • (j : E) := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          simp [k, sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
        _ = ∑ j : t, k j • (j : E) + ∑ j : t, (θ * μ j) • (j : E) := by
          simp [add_smul, Finset.sum_add_distrib]
        _ = ∑ j : t, k j • (j : E) + θ • ∑ j : t, μ j • (j : E) := by
          rw [← hscaled_relation]
    calc
      x = ∑ j : t, coeff j • (j : E) := hcoeff_sum
      _ = ∑ j : t, k j • (j : E) + θ • ∑ j : t, μ j • (j : E) := hk_decomp
      _ = ∑ j : t, k j • (j : E) := by
        rw [hμsum]
        simp
  let coeffErase : t.erase i₀ → 𝕜 := fun j ↦ k ⟨j, Finset.mem_of_mem_erase j.property⟩
  have hk_sum_erase :
      x = ∑ j : t.erase i₀, coeffErase j • (j : E) := by
    let g : E → E := fun y ↦ if hy : y ∈ t then k ⟨y, hy⟩ • y else 0
    have hf_erase :
        Finset.sum t g = Finset.sum (t.erase i₀) g := by
      rw [← Finset.sum_erase_add (s := t) (f := g) (a := i₀) i₀.property]
      simp [g, hk_i₀]
    -- Remove the zero coefficient at the chosen generator before repackaging the witness.
    calc
      x = ∑ j : t, k j • (j : E) := hk_sum
      _ = Finset.sum t g := by
        simpa [g] using (Finset.sum_coe_sort t g)
      _ = Finset.sum (t.erase i₀) g := hf_erase
      _ = ∑ j : t.erase i₀, coeffErase j • (j : E) := by
        calc
          Finset.sum (t.erase i₀) g = ∑ j : t.erase i₀, g (j : E) := by
            exact (Finset.sum_coe_sort (t.erase i₀) g).symm
          _ = ∑ j : t.erase i₀, coeffErase j • (j : E) := by
            apply Fintype.sum_congr
            intro j
            have hj_mem : (j : E) ∈ t := Finset.mem_of_mem_erase j.property
            simp [g, coeffErase, hj_mem]
  refine ⟨i₀, mem_hull_finset_of_nonnegCoeff_sum_subtype (t := t.erase i₀) coeffErase ?_ hk_sum_erase⟩
  intro j
  exact hk_nonneg ⟨j, Finset.mem_of_mem_erase j.property⟩

/-- Helper for Theorem 3.40: repeatedly erasing dependent generators produces a linearly
independent finite support that still contains the same vector in its cone hull. -/
lemma exists_linearIndependent_subset_of_mem_hull_finset [DecidableEq E] {t : Finset E} {x : E}
    (hx : x ∈ PointedCone.hull 𝕜 (↑t : Set E)) :
    ∃ u : Finset E, u ⊆ t ∧ LinearIndependent 𝕜 (fun i : u => (i : E)) ∧
      x ∈ PointedCone.hull 𝕜 (↑u : Set E) := by
  classical
  refine Finset.strongInductionOn t ?_ hx
  intro s ih hs
  by_cases hs_ind : LinearIndependent 𝕜 (fun i : s => (i : E))
  · exact ⟨s, subset_rfl, hs_ind, hs⟩
  · obtain ⟨y, hy⟩ := mem_hull_finset_erase_of_not_linearIndependent (t := s) hs_ind hs
    obtain ⟨u, hu_subset, hu_ind, hu_hull⟩ := ih (s.erase y) (Finset.erase_ssubset y.property) hy
    exact ⟨u, hu_subset.trans (Finset.erase_subset _ _), hu_ind, hu_hull⟩

section FiniteDimensional

variable [FiniteDimensional 𝕜 E]

/-- Theorem 3.40 (Carathéodory). If `v` is a conic combination of vectors in `X`, then `v` is a
conic combination of at most `dim(X)` linearly independent vectors in `X`, where the dimension is
taken to be the dimension of the linear span of `X`. -/
theorem exists_linearIndependent_conicCombination_of_mem_hull
    {X : Set E} {v : E} (hv : v ∈ PointedCone.hull 𝕜 X) :
    ∃ q : ℕ, ∃ r : Fin q → E, (∀ j, r j ∈ X) ∧ LinearIndependent 𝕜 r ∧
      q ≤ Module.finrank 𝕜 (Submodule.span 𝕜 X) ∧
      ∃ coeff : Fin q → 𝕜, (∀ j, 0 ≤ coeff j) ∧ v = ∑ j, coeff j • r j := by
  classical
  rw [PointedCone.mem_hull_set] at hv
  obtain ⟨c, hcX, hcoeff, hsum⟩ := hv
  let s : Finset E := c.support.erase 0
  have hv_s : v ∈ PointedCone.hull 𝕜 (↑s : Set E) := by
    -- Route correction: work directly on the nonzero support of the original cone witness instead
    -- of detouring through a normalized convex-hull subset.
    refine mem_hull_finset_of_nonnegCoeff_sum_subtype (t := s) (coeff := fun i ↦ c i) ?_ ?_
    · intro i
      exact hcoeff i
    · calc
        v = Finset.sum c.support (fun y ↦ c y • y) := by simpa [Finsupp.sum] using hsum.symm
        _ = Finset.sum s (fun y ↦ c y • y) := by
          by_cases h0 : (0 : E) ∈ c.support
          · rw [← Finset.insert_erase h0, Finset.sum_insert (Finset.notMem_erase 0 c.support)]
            simp [s]
          · simp [s, Finset.erase_eq_of_notMem h0]
        _ = ∑ i : s, c i • (i : E) := by
          simpa using (Finset.sum_coe_sort s (fun y ↦ c y • y)).symm
  obtain ⟨u, hu_subset, hu_ind, hv_u⟩ :=
    exists_linearIndependent_subset_of_mem_hull_finset (t := s) hv_s
  obtain ⟨coeffU, hcoeffU, hv_sum⟩ :=
    exists_nonnegCoeff_sum_subtype_of_mem_hull_finset (t := u) hv_u
  let e : u ≃ Fin u.card := Finset.equivFin u
  let r : Fin u.card → E := fun j ↦ (e.symm j : E)
  let coeff : Fin u.card → 𝕜 := fun j ↦ coeffU (e.symm j)
  have hr_mem : ∀ j, r j ∈ X := by
    intro j
    have hs_mem : (e.symm j : E) ∈ s := hu_subset (e.symm j).property
    exact hcX (Finset.mem_of_mem_erase hs_mem)
  have hr_ind : LinearIndependent 𝕜 r := by
    -- Transport linear independence from the subtype support to the canonical `Fin` indexing.
    exact hu_ind.comp e.symm e.symm.injective
  have hrange_subset : Set.range r ⊆ X := by
    rintro _ ⟨j, rfl⟩
    exact hr_mem j
  have hcard : u.card ≤ Module.finrank 𝕜 (Submodule.span 𝕜 X) := by
    calc
      u.card = Module.finrank 𝕜 (Submodule.span 𝕜 (Set.range r)) := by
        simpa [r] using (finrank_span_eq_card hr_ind).symm
      _ ≤ Module.finrank 𝕜 (Submodule.span 𝕜 X) := by
        exact Submodule.finrank_mono (Submodule.span_mono hrange_subset)
  have hv_fin :
      v = ∑ j : Fin u.card, coeff j • r j := by
    -- Reindex the subtype-indexed conic combination onto `Fin u.card`.
    calc
      v = ∑ i : u, coeffU i • (i : E) := hv_sum
      _ = ∑ j : Fin u.card, coeffU (e.symm j) • ((e.symm j : u) : E) := by
        exact
          (Fintype.sum_equiv e.symm _ (fun i : u ↦ coeffU i • (i : E))
            (fun j ↦ rfl)).symm
  refine ⟨u.card, r, hr_mem, hr_ind, hcard, coeff, ?_, hv_fin⟩
  intro j
  exact hcoeffU (e.symm j)

end FiniteDimensional
