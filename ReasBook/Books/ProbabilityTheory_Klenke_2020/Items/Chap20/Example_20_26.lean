/-
Authors: Xuanzhi Ren
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@cdaedff51aa8473d10341ae5afb27386db4d11c1:ReasBook/Books/ProbabilityTheory_Klenke_2020/README.md (formalization contributor).
-/

import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Definition_20_24
import Books.ProbabilityTheory_Klenke_2020.Items.Chap20.Remark_20_25
import Mathlib

-- Declarations for this item will be appended below by the statement pipeline.

open MeasureTheory ProbabilityTheory Filter
open scoped symmDiff

universe u v

local instance {E : Type u} [MeasurableSpace E] : MeasurableSpace (Stream' E) :=
  inferInstanceAs (MeasurableSpace (ℕ → E))

local instance {ι : Type*} {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∀ i : ι, IsProbabilityMeasure ((fun _ : ι ↦ μ) i) :=
  fun _ ↦ inferInstance

/-- Helper for Example 20.26: cylinder events on disjoint coordinate sets are independent under an
i.i.d. product measure. -/
lemma productCylinderEvents_indep_of_disjoint {ι : Type*} {E : Type u} [MeasurableSpace E]
    (μ : Measure E) [IsProbabilityMeasure μ] {S T : Set ι} (hST : Disjoint S T) :
    Indep (MeasureTheory.cylinderEvents (X := fun _ : ι ↦ E) S)
      (MeasureTheory.cylinderEvents (X := fun _ : ι ↦ E) T)
      (Measure.infinitePi (fun _ : ι ↦ μ)) := by
  let m : ι → MeasurableSpace (∀ _ : ι, E) :=
    fun i ↦ MeasurableSpace.comap (fun ω : ∀ _ : ι, E ↦ ω i) inferInstance
  have hIndepFun :
      iIndepFun (fun i (ω : ∀ _ : ι, E) ↦ ω i) (Measure.infinitePi (fun _ : ι ↦ μ)) := by
    -- The coordinate projections on the product space are i.i.d. by the defining property of
    -- `Measure.infinitePi`.
    simpa using
      (iIndepFun_infinitePi (P := fun _ : ι ↦ μ) (X := fun _ ↦ id)
        fun _ ↦ measurable_id)
  have hIndep : iIndep m (Measure.infinitePi (fun _ : ι ↦ μ)) := by
    -- Repackage coordinate independence as independence of the coordinate `comap` sigma-algebras.
    simpa [m] using hIndepFun.iIndep (m := fun _ : ι ↦ inferInstance)
  have hLe : ∀ i, m i ≤ MeasurableSpace.pi := by
    -- Each coordinate sigma-algebra is contained in the product sigma-algebra.
    intro i
    exact (measurable_pi_apply i).comap_le
  -- The cylinder-event sigma-algebras are the joins of the coordinate `comap`s on the chosen
  -- supports, so `indep_iSup_of_disjoint` applies directly.
  simpa [MeasureTheory.cylinderEvents, m] using
    (indep_iSup_of_disjoint (μ := Measure.infinitePi (fun _ : ι ↦ μ)) hLe hIndep hST)

/-- Helper for Example 20.26: a measurable cylinder on support `s` is measurable for the
finite-support sigma-algebra `cylinderEvents (s : Set ι)`. -/
lemma measurableSet_cylinderEvents_cylinder {ι : Type*} {E : Type u} [MeasurableSpace E]
    (s : Finset ι) {S : Set ((i : s) → E)} (hS : MeasurableSet S) :
    MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ι ↦ E) (s : Set ι)]
      (MeasureTheory.cylinder s S) := by
  -- A cylinder is the preimage of its base set under the restriction map to the finite support.
  simpa [MeasureTheory.cylinder] using
    hS.preimage
      (MeasureTheory.measurable_restrict_cylinderEvents (X := fun _ : ι ↦ E) (s : Set ι))

/-- Helper for Example 20.26: iterating `Stream'.tail` shifts coordinates by the same amount. -/
lemma iterateTail_apply {E : Type u} [MeasurableSpace E]
    (ω : Stream' E) (n k : ℕ) :
    (Stream'.tail^[n]) ω k = ω (n + k) := by
  induction n generalizing ω k with
  | zero =>
      -- With zero iterates there is no shift, so the coordinate stays at `k`.
      simp
  | succ n ih =>
      -- One further iterate applies `Stream'.tail` once and then reuses the induction hypothesis.
      rw [Function.iterate_succ, Function.comp_apply]
      simpa [Stream'.tail, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (ω := Stream'.tail ω) (k := k)

/-- Helper for Example 20.26: iterating the bilateral shift translates coordinates by the iterate
count. -/
lemma iterateBilateralShift_apply {E : Type u} [MeasurableSpace E]
    (ω : ℤ → E) (n : ℕ) (k : ℤ) :
    ((fun ω : ℤ → E ↦ fun j : ℤ ↦ ω (j + 1))^[n]) ω k = ω (k + n) := by
  induction n generalizing ω k with
  | zero =>
      -- Zero iterates leave every coordinate unchanged.
      simp
  | succ n ih =>
      -- One more iterate applies the shift once and then reuses the induction hypothesis.
      rw [Function.iterate_succ, Function.comp_apply]
      simpa [Int.add_assoc, Int.add_left_comm, Int.add_comm] using
        ih (ω := fun j : ℤ ↦ ω (j + 1)) (k := k)

/-- Helper for Example 20.26: preimages of finite-coordinate boxes under `Stream'.tail` are the
corresponding shifted boxes. -/
private lemma tail_preimage_pi {E : Type u} [MeasurableSpace E] (s : Finset ℕ) (t : ℕ → Set E) :
    Stream'.tail ⁻¹' Set.pi s t =
      Set.pi (s.image Nat.succ) (fun n ↦ if n ∈ s.image Nat.succ then t (n - 1) else Set.univ) := by
  -- Replace the old `change`-heavy route with a direct membership calculation on finite boxes.
  ext ω
  simp only [Set.mem_preimage]
  constructor
  · intro h
    change ∀ n, n ∈ s → (Stream'.tail ω) n ∈ t n at h
    change ∀ n, n ∈ s.image Nat.succ →
        ω n ∈ (if n ∈ s.image Nat.succ then t (n - 1) else Set.univ)
    intro n hn
    rcases Finset.mem_image.mp hn with ⟨j, hj, rfl⟩
    simpa [Stream'.tail] using h j
  · intro h
    change ∀ n, n ∈ s.image Nat.succ →
        ω n ∈ (if n ∈ s.image Nat.succ then t (n - 1) else Set.univ) at h
    change ∀ n, n ∈ s → (Stream'.tail ω) n ∈ t n
    intro n hn
    have hshift : ω (n + 1) ∈
        (if n + 1 ∈ s.image Nat.succ then t ((n + 1) - 1) else Set.univ) :=
      h (n + 1) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
    simpa [Stream'.tail, Finset.mem_image, hn] using hshift

/-- Helper for Example 20.26: the one-sided shift on `E^ℕ` is measurable coordinatewise. -/
private theorem measurable_tail {E : Type u} [MeasurableSpace E] :
    Measurable (Stream'.tail : Stream' E → Stream' E) := by
  -- Each coordinate of the tail map is the next coordinate projection.
  refine measurable_pi_lambda _ fun i ↦ ?_
  simpa [Stream'.tail] using (measurable_pi_apply (i + 1 : ℕ))

/-- Helper for Example 20.26: the one-sided Bernoulli shift preserves the i.i.d. product
measure. -/
lemma oneSidedShift_measurePreserving {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    MeasurePreserving Stream'.tail
      (Measure.infinitePi (fun _ : ℕ ↦ μ))
      (Measure.infinitePi (fun _ : ℕ ↦ μ)) := by
  classical
  refine ⟨measurable_tail, ?_⟩
  -- Match the pushed-forward measure with the product measure on finite-coordinate boxes.
  apply Measure.eq_infinitePi (μ := fun _ : ℕ ↦ μ)
  intro s t ht
  have hmap :
      (Measure.map Stream'.tail (Measure.infinitePi fun _ : ℕ ↦ μ)) (Set.pi s t) =
        (Measure.infinitePi fun _ : ℕ ↦ μ) (Stream'.tail ⁻¹' Set.pi s t) := by
    simpa using
      (Measure.map_apply (μ := Measure.infinitePi fun _ : ℕ ↦ μ) measurable_tail
        (.pi s.countable_toSet fun i _ ↦ ht i))
  exact hmap.trans <| by
    calc
      (Measure.infinitePi fun _ : ℕ ↦ μ) (Stream'.tail ⁻¹' Set.pi s t) =
          (Measure.infinitePi fun _ : ℕ ↦ μ)
            (Set.pi (s.image Nat.succ)
              (fun n ↦ if n ∈ s.image Nat.succ then t (n - 1) else Set.univ)) := by
            exact congrArg (Measure.infinitePi fun _ : ℕ ↦ μ) (tail_preimage_pi (E := E) s t)
      _ = ∏ i ∈ s, μ (t i) := by
        rw [Measure.infinitePi_pi (μ := fun _ : ℕ ↦ μ) (s := s.image Nat.succ)
          (t := fun n ↦ if n ∈ s.image Nat.succ then t (n - 1) else Set.univ)]
        · rw [Finset.prod_image]
          · refine Finset.prod_congr rfl ?_
            intro i hi
            simp [hi]
          · intro a _ b _ hab
            exact Nat.succ_injective hab
        · intro i hi
          simp [hi, ht]

/-- Helper for Example 20.26: the bilateral Bernoulli shift preserves the i.i.d. product
measure. -/
lemma bilateralShift_measurePreserving {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1))
      (Measure.infinitePi (fun _ : ℤ ↦ μ))
      (Measure.infinitePi (fun _ : ℤ ↦ μ)) := by
  let e : ℤ ≃ ℤ := (Equiv.addRight (1 : ℤ)).symm
  have hshift :
      (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1)) =
        MeasurableEquiv.piCongrLeft (fun _ : ℤ ↦ E) e := by
    -- The `piCongrLeft` reindexing by translation is exactly the bilateral shift.
    ext ω n
    simp [e, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft, Equiv.addRight]
  refine ⟨hshift ▸ (MeasurableEquiv.piCongrLeft (fun _ : ℤ ↦ E) e).measurable, ?_⟩
  -- Reindex the coordinates by the translation equivalence on `ℤ`.
  simpa [hshift] using
    (Measure.infinitePi_map_piCongrLeft (X := fun _ : ℤ ↦ E) (μ := fun _ : ℤ ↦ μ) e)

/-- Helper for Example 20.26: in the one-sided index set, a sufficiently large forward shift moves
every finite support strictly past another fixed finite support. -/
private lemma eventuallyDisjointShiftedSupportsNat (s t : Finset ℕ) :
    ∃ N : ℕ, ∀ n ≥ N, Disjoint s (t.image fun k ↦ n + k) := by
  refine ⟨s.sup id + 1, ?_⟩
  intro n hn
  refine Finset.disjoint_left.mpr ?_
  intro x hxS hxT
  rcases Finset.mem_image.mp hxT with ⟨k, hk, rfl⟩
  -- Every element of `s` is at most the support maximum, while every shifted element is at least
  -- `n`, hence strictly larger once `n > s.sup id`.
  have hkle : n + k ≤ s.sup id := by
    simpa using (Finset.le_sup (f := id) hxS)
  have hgt : s.sup id < n + k := by
    have hn' : s.sup id + 1 ≤ n + k := le_trans hn (Nat.le_add_right n k)
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (s.sup id)) hn'
  exact (not_lt_of_ge hkle hgt).elim

/-- Helper for Example 20.26: on `ℤ`, sufficiently large positive shifts move one finite support
strictly to the right of another fixed finite support. -/
private lemma eventuallyDisjointShiftedSupportsInt (s t : Finset ℤ) :
    ∃ N : ℕ, ∀ n ≥ N, Disjoint s (t.image fun k : ℤ ↦ k + n) := by
  classical
  by_cases hs : s.Nonempty
  · by_cases ht : t.Nonempty
    · refine ⟨Int.toNat (s.max' hs) + Int.toNat (-t.min' ht) + 1, ?_⟩
      intro n hn
      refine Finset.disjoint_left.mpr ?_
      intro x hxS hxT
      rcases Finset.mem_image.mp hxT with ⟨k, hk, hkx⟩
      -- Elements of `s` are bounded by `s.max' hs`, while shifted elements of `t` are eventually
      -- at least `t.min' ht + n`.
      have hxle : x ≤ s.max' hs := by
        exact Finset.le_max' s x hxS
      have hkinf : t.min' ht ≤ k := by
        exact Finset.min'_le t k hk
      have hsBound : s.max' hs ≤ (Int.toNat (s.max' hs) : ℤ) := by
        by_cases hnonneg : 0 ≤ s.max' hs
        · simpa [Int.toNat_of_nonneg hnonneg] using hnonneg
        · have hle : s.max' hs ≤ 0 := le_of_not_ge hnonneg
          have hnat : (0 : ℤ) ≤ Int.toNat (s.max' hs) := by
            exact_mod_cast Nat.zero_le (Int.toNat (s.max' hs))
          linarith
      have htBound : -t.min' ht ≤ (Int.toNat (-t.min' ht) : ℤ) := by
        by_cases hnonneg : 0 ≤ -t.min' ht
        · simpa [Int.toNat_of_nonneg hnonneg] using hnonneg
        · have hle : -t.min' ht ≤ 0 := le_of_not_ge hnonneg
          have hnat : (0 : ℤ) ≤ Int.toNat (-t.min' ht) := by
            exact_mod_cast Nat.zero_le (Int.toNat (-t.min' ht))
          linarith
      have hn' : ((Int.toNat (s.max' hs) + Int.toNat (-t.min' ht) + 1 : ℕ) : ℤ) ≤ n := by
        exact_mod_cast hn
      have hshift : s.max' hs + 1 - t.min' ht ≤ n := by
        calc
          s.max' hs + 1 - t.min' ht = s.max' hs + 1 + (-t.min' ht) := by ring
          _ ≤ (Int.toNat (s.max' hs) : ℤ) + 1 + Int.toNat (-t.min' ht) := by
            linarith
          _ = ((Int.toNat (s.max' hs) + Int.toNat (-t.min' ht) + 1 : ℕ) : ℤ) := by
            simp [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
          _ ≤ n := hn'
      have hgt : s.max' hs < k + n := by
        have hle : s.max' hs + 1 ≤ k + n := by
          linarith
        linarith
      have : ¬ x < x := lt_irrefl x
      rw [hkx] at hgt
      exact this (lt_of_le_of_lt hxle hgt)
    · refine ⟨0, ?_⟩
      intro n hn
      simp [Finset.not_nonempty_iff_eq_empty.mp ht]
  · refine ⟨0, ?_⟩
    intro n hn
    simp [Finset.not_nonempty_iff_eq_empty.mp hs]

/-- Helper for Example 20.26: if two pairs of events are close in symmetric difference, then the
corresponding correlation terms differ by the approximant correlation error plus the two
approximation errors. -/
private lemma correlationErrorBound_ofApprox {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {A A' C C' : Set Ω}
    (hA : MeasurableSet A) (hA' : MeasurableSet A')
    (hC : MeasurableSet C) (hC' : MeasurableSet C') :
    |P.real (A ∩ C) - P.real A * P.real C|
      ≤ (|P.real (A' ∩ C') - P.real A' * P.real C'| +
          2 * P.real (A ∆ A') + 2 * P.real (C ∆ C')) := by
  have hInterSubsetA : (A ∩ C) ∆ (A' ∩ C) ⊆ A ∆ A' := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    rcases hx with ⟨hxAC, hxA'C⟩ | ⟨hxA'C, hxAC⟩
    · by_cases hxA' : x ∈ A'
      · right
        refine ⟨hxA', ?_⟩
        intro hxA
        exact hxA'C ⟨hxA', hxAC.2⟩
      · exact Or.inl ⟨hxAC.1, hxA'⟩
    · by_cases hxA : x ∈ A
      · left
        refine ⟨hxA, ?_⟩
        intro hxA'
        exact hxAC ⟨hxA, hxA'C.2⟩
      · exact Or.inr ⟨hxA'C.1, hxA⟩
  have hInterSubsetC : (A' ∩ C) ∆ (A' ∩ C') ⊆ C ∆ C' := by
    intro x hx
    simp only [Set.mem_symmDiff, Set.mem_inter_iff] at hx ⊢
    rcases hx with ⟨hxA'C, hxA'C'⟩ | ⟨hxA'C', hxA'C⟩
    · by_cases hxC' : x ∈ C'
      · right
        refine ⟨hxC', ?_⟩
        intro hxC
        exact hxA'C' ⟨hxA'C.1, hxC'⟩
      · exact Or.inl ⟨hxA'C.2, hxC'⟩
    · by_cases hxC : x ∈ C
      · left
        refine ⟨hxC, ?_⟩
        intro hxC'
        exact hxA'C ⟨hxA'C'.1, hxC⟩
      · exact Or.inr ⟨hxA'C'.2, hxC⟩
  have hInterA :
      |P.real (A ∩ C) - P.real (A' ∩ C)| ≤ P.real (A ∆ A') := by
    -- First freeze the second event and only compare the first one.
    refine le_trans ?_ (measureReal_mono (μ := P) hInterSubsetA)
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := (hA.inter hC).nullMeasurableSet) (ht := (hA'.inter hC).nullMeasurableSet))
  have hInterC :
      |P.real (A' ∩ C) - P.real (A' ∩ C')| ≤ P.real (C ∆ C') := by
    -- Then freeze the approximating first event and compare the second one.
    refine le_trans ?_ (measureReal_mono (μ := P) hInterSubsetC)
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := (hA'.inter hC).nullMeasurableSet) (ht := (hA'.inter hC').nullMeasurableSet))
  have hAErr :
      |P.real A - P.real A'| ≤ P.real (A ∆ A') := by
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := hA.nullMeasurableSet) (ht := hA'.nullMeasurableSet))
  have hCErr :
      |P.real C - P.real C'| ≤ P.real (C ∆ C') := by
    simpa using
      (abs_measureReal_sub_le_measureReal_symmDiff (μ := P)
        (hs := hC.nullMeasurableSet) (ht := hC'.nullMeasurableSet))
  have hA_nonneg : 0 ≤ P.real A := by positivity
  have hA'_nonneg : 0 ≤ P.real A' := by positivity
  have hC_nonneg : 0 ≤ P.real C := by positivity
  have hC'_nonneg : 0 ≤ P.real C' := by positivity
  have hA_le_one : P.real A ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ A) : P.real A ≤ P.real Set.univ)
  have hA'_le_one : P.real A' ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ A') : P.real A' ≤ P.real Set.univ)
  have hC_le_one : P.real C ≤ 1 := by
    simpa using (measureReal_mono (μ := P) (Set.subset_univ C) : P.real C ≤ P.real Set.univ)
  have hProdA :
      |P.real A * P.real C - P.real A' * P.real C| ≤ P.real (A ∆ A') := by
    have hmul :
        P.real A * P.real C - P.real A' * P.real C =
          (P.real A - P.real A') * P.real C := by
      ring
    calc
      |P.real A * P.real C - P.real A' * P.real C|
          = |P.real A - P.real A'| * P.real C := by
              rw [hmul, abs_mul, abs_of_nonneg hC_nonneg]
      _ ≤ |P.real A - P.real A'| * 1 := by
            gcongr
      _ = |P.real A - P.real A'| := by ring
      _ ≤ P.real (A ∆ A') := hAErr
  have hProdC :
      |P.real A' * P.real C - P.real A' * P.real C'| ≤ P.real (C ∆ C') := by
    have hmul :
        P.real A' * P.real C - P.real A' * P.real C' =
          P.real A' * (P.real C - P.real C') := by
      ring
    calc
      |P.real A' * P.real C - P.real A' * P.real C'|
          = P.real A' * |P.real C - P.real C'| := by
              rw [hmul, abs_mul, abs_of_nonneg hA'_nonneg]
      _ ≤ 1 * |P.real C - P.real C'| := by
            gcongr
      _ = |P.real C - P.real C'| := by ring
      _ ≤ P.real (C ∆ C') := hCErr
  have hInter :
      |P.real (A ∩ C) - P.real (A' ∩ C')|
        ≤ P.real (A ∆ A') + P.real (C ∆ C') := by
    calc
      |P.real (A ∩ C) - P.real (A' ∩ C')|
          ≤ |P.real (A ∩ C) - P.real (A' ∩ C)| +
              |P.real (A' ∩ C) - P.real (A' ∩ C')| := by
                simpa using
                  (abs_sub_le (P.real (A ∩ C)) (P.real (A' ∩ C)) (P.real (A' ∩ C')))
      _ ≤ P.real (A ∆ A') + P.real (C ∆ C') := add_le_add hInterA hInterC
  have hProd :
      |P.real A' * P.real C' - P.real A * P.real C|
        ≤ P.real (A ∆ A') + P.real (C ∆ C') := by
    calc
      |P.real A' * P.real C' - P.real A * P.real C|
          ≤ |P.real A' * P.real C' - P.real A' * P.real C| +
              |P.real A' * P.real C - P.real A * P.real C| := by
                simpa [abs_sub_comm, add_comm, add_left_comm, add_assoc] using
                  (abs_sub_le (P.real A' * P.real C') (P.real A' * P.real C)
                    (P.real A * P.real C))
      _ ≤ P.real (C ∆ C') + P.real (A ∆ A') := by
            refine add_le_add ?_ ?_
            simpa [abs_sub_comm] using hProdC
            simpa [abs_sub_comm] using hProdA
      _ = P.real (A ∆ A') + P.real (C ∆ C') := by ring
  -- Combine the intersection error, the approximant correlation term, and the product error.
  have hApproxCorr :
      |P.real (A' ∩ C') - P.real A * P.real C|
        ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C')) := by
    calc
      |P.real (A' ∩ C') - P.real A * P.real C|
          ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
              |P.real A' * P.real C' - P.real A * P.real C| := by
                simpa using
                  (abs_sub_le (P.real (A' ∩ C')) (P.real A' * P.real C')
                    (P.real A * P.real C))
      _ ≤ |P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C')) := by
              simpa [add_comm, add_left_comm, add_assoc] using
                add_le_add_left hProd
                  (|P.real (A' ∩ C') - P.real A' * P.real C'|)
  calc
    |P.real (A ∩ C) - P.real A * P.real C|
        ≤ |P.real (A ∩ C) - P.real (A' ∩ C')| +
            |P.real (A' ∩ C') - P.real A * P.real C| := by
              simpa using
                (abs_sub_le (P.real (A ∩ C)) (P.real (A' ∩ C')) (P.real A * P.real C))
    _ ≤ (P.real (A ∆ A') + P.real (C ∆ C')) +
          (|P.real (A' ∩ C') - P.real A' * P.real C'| +
            (P.real (A ∆ A') + P.real (C ∆ C'))) := by
              exact add_le_add hInter hApproxCorr
    _ = |P.real (A' ∩ C') - P.real A' * P.real C'| +
          2 * P.real (A ∆ A') + 2 * P.real (C ∆ C') := by
            ring

-- Proof sketch: approximate arbitrary measurable events in the one-sided product space by
-- cylinder events depending on finitely many coordinates. For sufficiently large shifts, the
-- coordinate supports of the two cylinder approximants are disjoint, so independence under the
-- product measure makes the shifted intersection factor. Passing from cylinders to general
-- measurable sets yields the mixing criterion for the canonical one-sided shift `Stream'.tail`.
/-- Example 20.26: the one-sided Bernoulli product shift on `E^ℕ` is mixing. The bilateral case
is stated separately below. -/
theorem iid_oneSided_product_shift_is_mixing {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    let P : Measure (Stream' E) := Measure.infinitePi (fun _ : ℕ ↦ μ)
    letI : IsProbabilityMeasure P := by
      change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
      infer_instance
    MeasurePreserving Stream'.tail P P ∧ IsStronglyMixing Stream'.tail P :=
    by
  let P : Measure (Stream' E) := Measure.infinitePi (fun _ : ℕ ↦ μ)
  letI : IsProbabilityMeasure P := by
    change IsProbabilityMeasure (Measure.infinitePi (fun _ : ℕ ↦ μ))
    infer_instance
  have hPres : MeasurePreserving Stream'.tail P P := by
    -- Route correction: isolate the measure-preserving half first, so the remaining work is only
    -- the finite-support approximation argument for strong mixing.
    simpa [P] using oneSidedShift_measurePreserving (E := E) μ
  refine ⟨hPres, ?_⟩
  intro A B hA hB
  have hdense : P.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E)) := by
    -- Finite-coordinate cylinders form a measure-dense set algebra for the product space.
    refine Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ := P)
        (𝒜 := MeasureTheory.measurableCylinders (fun _ : ℕ ↦ E))
        MeasureTheory.isSetAlgebra_measurableCylinders ?_
    simpa using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℕ ↦ E)).symm
  -- Approximate `A` and `B` by finite-coordinate cylinders, then separate those supports by a
  -- sufficiently large forward shift.
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by
    positivity
  rcases hdense.fin_meas_approx hA (measure_ne_top P A) δ hδ with
    ⟨Aε, hAε_mem, -, hAε_close⟩
  rcases hdense.fin_meas_approx hB (measure_ne_top P B) δ hδ with
    ⟨Bε, hBε_mem, -, hBε_close⟩
  let sA : Finset ℕ := MeasureTheory.measurableCylinders.finset hAε_mem
  let SA : Set ((i : sA) → E) := MeasureTheory.measurableCylinders.set hAε_mem
  let sB : Finset ℕ := MeasureTheory.measurableCylinders.finset hBε_mem
  let SB : Set ((i : sB) → E) := MeasureTheory.measurableCylinders.set hBε_mem
  have hAε_eq : Aε = MeasureTheory.cylinder sA SA :=
    MeasureTheory.measurableCylinders.eq_cylinder hAε_mem
  have hBε_eq : Bε = MeasureTheory.cylinder sB SB :=
    MeasureTheory.measurableCylinders.eq_cylinder hBε_mem
  have hAε : MeasurableSet Aε := MeasurableSet.of_mem_measurableCylinders hAε_mem
  have hBε : MeasurableSet Bε := MeasurableSet.of_mem_measurableCylinders hBε_mem
  have hSA : MeasurableSet SA := MeasureTheory.measurableCylinders.measurableSet hAε_mem
  have hSB : MeasurableSet SB := MeasureTheory.measurableCylinders.measurableSet hBε_mem
  have hAε_cyl :
      MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sA : Set ℕ)] Aε := by
    -- Place the approximating cylinder for `A` in the sigma-algebra of its finite support.
    rw [hAε_eq]
    exact measurableSet_cylinderEvents_cylinder (E := E) sA hSA
  obtain ⟨N, hN⟩ := eventuallyDisjointShiftedSupportsNat sA sB
  refine ⟨N, ?_⟩
  intro n hn
  let sBn : Finset ℕ := sB.image fun k ↦ n + k
  have hDisjFinset : Disjoint sA sBn := by
    simpa [sBn] using hN n hn
  have hDisj : Disjoint (sA : Set ℕ) (sBn : Set ℕ) := Finset.disjoint_coe.2 hDisjFinset
  have hShiftMeas :
      @Measurable (Stream' E) (Stream' E)
        (MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sBn : Set ℕ))
        (MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sB : Set ℕ))
        (Stream'.tail^[n]) := by
    -- On the translated support, each coordinate of `tail^[n]` is just a coordinate projection.
    refine (MeasureTheory.measurable_cylinderEvents_iff (Δ := (sB : Set ℕ))).2 ?_
    intro i hi
    have hi' : n + i ∈ (sBn : Set ℕ) := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simpa [sBn, iterateTail_apply] using
      (MeasureTheory.measurable_cylinderEvent_apply
        (X := fun _ : ℕ ↦ E) (Δ := (sBn : Set ℕ)) hi')
  have hShiftBε :
      MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sBn : Set ℕ)]
        ((Stream'.tail^[n]) ⁻¹' Bε) := by
    -- Pull the cylinder approximation for `B` back through the iterate inside that shifted
    -- coordinate sigma-algebra.
    rw [hBε_eq]
    exact (measurableSet_cylinderEvents_cylinder (E := E) sB hSB).preimage hShiftMeas
  have hIndep :
      Indep (MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sA : Set ℕ))
        (MeasureTheory.cylinderEvents (X := fun _ : ℕ ↦ E) (sBn : Set ℕ)) P := by
    -- Disjoint coordinate blocks are independent under the product law.
    simpa [P, sBn] using
      (productCylinderEvents_indep_of_disjoint (ι := ℕ) (E := E) μ
        (S := (sA : Set ℕ)) (T := (sBn : Set ℕ)) hDisj)
  have hIndepSet : IndepSet Aε ((Stream'.tail^[n]) ⁻¹' Bε) P :=
    hIndep.indepSet_of_measurableSet hAε_cyl hShiftBε
  have hApproxReal :
      P.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' Bε) =
        P.real Aε * P.real ((Stream'.tail^[n]) ⁻¹' Bε) := by
    -- Independence makes the cylinder approximant correlation exactly vanish.
    simpa [Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal hIndepSet.measure_inter_eq_mul
  have hPreB : MeasurableSet ((Stream'.tail^[n]) ⁻¹' B) :=
    hB.preimage (hPres.iterate n).measurable
  have hPreBε : MeasurableSet ((Stream'.tail^[n]) ⁻¹' Bε) :=
    hBε.preimage (hPres.iterate n).measurable
  have hPreBReal : P.real ((Stream'.tail^[n]) ⁻¹' B) = P.real B := by
    -- Measure preservation rewrites the pulled-back target event back to the original event.
    simpa [Measure.real_def] using
      congrArg ENNReal.toReal
        ((hPres.iterate n).measure_preimage (s := B) hB.nullMeasurableSet)
  have hAε_closeReal : P.real (A ∆ Aε) < δ := by
    simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hAε_close
  have hShiftBε_closeReal :
      P.real (((Stream'.tail^[n]) ⁻¹' B) ∆ ((Stream'.tail^[n]) ⁻¹' Bε)) < δ := by
    have hpre :
        P (((Stream'.tail^[n]) ⁻¹' B) ∆ ((Stream'.tail^[n]) ⁻¹' Bε)) = P (B ∆ Bε) := by
      rw [← Set.preimage_symmDiff]
      exact (hPres.iterate n).measure_preimage (s := B ∆ Bε) (hB.symmDiff hBε).nullMeasurableSet
    rw [show
        P.real (((Stream'.tail^[n]) ⁻¹' B) ∆ ((Stream'.tail^[n]) ⁻¹' Bε)) =
          P.real (B ∆ Bε) by
          simpa [Measure.real_def] using congrArg ENNReal.toReal hpre]
    simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hBε_close
  have hApproxBound :=
    correlationErrorBound_ofApprox (P := P) hA hAε hPreB hPreBε
  -- The exact cylinder factorization plus the two approximation errors give the required
  -- arbitrarily small bound.
  calc
    |P.real (A ∩ (Stream'.tail^[n]) ⁻¹' B) - P.real A * P.real B|
        = |P.real (A ∩ (Stream'.tail^[n]) ⁻¹' B) -
            P.real A * P.real ((Stream'.tail^[n]) ⁻¹' B)| := by
              rw [hPreBReal]
    _ ≤ |P.real (Aε ∩ (Stream'.tail^[n]) ⁻¹' Bε) -
          P.real Aε * P.real ((Stream'.tail^[n]) ⁻¹' Bε)| +
          2 * P.real (A ∆ Aε) +
          2 * P.real (((Stream'.tail^[n]) ⁻¹' B) ∆ ((Stream'.tail^[n]) ⁻¹' Bε)) := by
            simpa [add_assoc, add_left_comm, add_comm] using hApproxBound
    _ = 2 * P.real (A ∆ Aε) +
          2 * P.real (((Stream'.tail^[n]) ⁻¹' B) ∆ ((Stream'.tail^[n]) ⁻¹' Bε)) := by
            rw [hApproxReal]
            simp
    _ < ε := by
          dsimp [δ] at hAε_closeReal hShiftBε_closeReal ⊢
          nlinarith

-- Proof sketch: the same cylinder-approximation argument works on `E^ℤ`. Large forward shifts
-- separate the finite coordinate supports of the approximating cylinder events, and independence
-- under the product measure gives the required factorization, which implies mixing.
/-- The bilateral Bernoulli product shift on `E^ℤ` is mixing. -/
theorem iid_bilateral_product_shift_is_mixing {E : Type u} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    MeasurePreserving (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1))
      (Measure.infinitePi (fun _ : ℤ ↦ μ))
      (Measure.infinitePi (fun _ : ℤ ↦ μ)) ∧
      IsStronglyMixing (fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))
        (Measure.infinitePi (fun _ : ℤ ↦ μ)) :=
    by
  have hPres :
      MeasurePreserving (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1))
        (Measure.infinitePi (fun _ : ℤ ↦ μ))
        (Measure.infinitePi (fun _ : ℤ ↦ μ)) :=
    bilateralShift_measurePreserving (E := E) μ
  refine ⟨hPres, ?_⟩
  intro A B hA hB
  let P : Measure (ℤ → E) := Measure.infinitePi (fun _ : ℤ ↦ μ)
  have hPres' :
      MeasurePreserving (fun ω : ℤ → E ↦ fun n : ℤ ↦ ω (n + 1)) P P := by
    simpa [P] using hPres
  have hdense : P.MeasureDense (MeasureTheory.measurableCylinders (fun _ : ℤ ↦ E)) := by
    -- The bilateral product sigma-algebra is generated by the same finite-coordinate cylinders.
    refine Measure.MeasureDense.of_generateFrom_isSetAlgebra_finite
        (μ := P)
        (𝒜 := MeasureTheory.measurableCylinders (fun _ : ℤ ↦ E))
        MeasureTheory.isSetAlgebra_measurableCylinders ?_
    simpa using
      (MeasureTheory.generateFrom_measurableCylinders (α := fun _ : ℤ ↦ E)).symm
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  let δ : ℝ := ε / 8
  have hδ : 0 < δ := by
    positivity
  rcases hdense.fin_meas_approx hA (measure_ne_top P A) δ hδ with
    ⟨Aε, hAε_mem, -, hAε_close⟩
  rcases hdense.fin_meas_approx hB (measure_ne_top P B) δ hδ with
    ⟨Bε, hBε_mem, -, hBε_close⟩
  let sA : Finset ℤ := MeasureTheory.measurableCylinders.finset hAε_mem
  let SA : Set ((i : sA) → E) := MeasureTheory.measurableCylinders.set hAε_mem
  let sB : Finset ℤ := MeasureTheory.measurableCylinders.finset hBε_mem
  let SB : Set ((i : sB) → E) := MeasureTheory.measurableCylinders.set hBε_mem
  have hAε_eq : Aε = MeasureTheory.cylinder sA SA :=
    MeasureTheory.measurableCylinders.eq_cylinder hAε_mem
  have hBε_eq : Bε = MeasureTheory.cylinder sB SB :=
    MeasureTheory.measurableCylinders.eq_cylinder hBε_mem
  have hAε : MeasurableSet Aε := MeasurableSet.of_mem_measurableCylinders hAε_mem
  have hBε : MeasurableSet Bε := MeasurableSet.of_mem_measurableCylinders hBε_mem
  have hSA : MeasurableSet SA := MeasureTheory.measurableCylinders.measurableSet hAε_mem
  have hSB : MeasurableSet SB := MeasureTheory.measurableCylinders.measurableSet hBε_mem
  have hAε_cyl :
      MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sA : Set ℤ)] Aε := by
    -- Place the approximation for `A` in the sigma-algebra determined by its finite support.
    rw [hAε_eq]
    exact measurableSet_cylinderEvents_cylinder (E := E) sA hSA
  obtain ⟨N, hN⟩ := eventuallyDisjointShiftedSupportsInt sA sB
  refine ⟨N, ?_⟩
  intro n hn
  let sBn : Finset ℤ := sB.image fun k : ℤ ↦ k + n
  have hDisjFinset : Disjoint sA sBn := by
    simpa [sBn] using hN n hn
  have hDisj : Disjoint (sA : Set ℤ) (sBn : Set ℤ) := Finset.disjoint_coe.2 hDisjFinset
  have hShiftMeas :
      @Measurable (ℤ → E) (ℤ → E)
        (MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sBn : Set ℤ))
        (MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sB : Set ℤ))
        ((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) := by
    -- The `n`-fold bilateral shift translates the finite support by `k ↦ k + n`.
    refine (MeasureTheory.measurable_cylinderEvents_iff (Δ := (sB : Set ℤ))).2 ?_
    intro i hi
    have hi' : i + n ∈ (sBn : Set ℤ) := by
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
    simpa [sBn, iterateBilateralShift_apply] using
      (MeasureTheory.measurable_cylinderEvent_apply
        (X := fun _ : ℤ ↦ E) (Δ := (sBn : Set ℤ)) hi')
  have hShiftBε :
      MeasurableSet[MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sBn : Set ℤ)]
        (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε) := by
    -- Pull the approximation for `B` back through the translated support sigma-algebra.
    rw [hBε_eq]
    exact (measurableSet_cylinderEvents_cylinder (E := E) sB hSB).preimage hShiftMeas
  have hIndep :
      Indep (MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sA : Set ℤ))
        (MeasureTheory.cylinderEvents (X := fun _ : ℤ ↦ E) (sBn : Set ℤ)) P := by
    -- The bilateral product measure has the same disjoint-coordinate independence property.
    simpa [P, sBn] using
      (productCylinderEvents_indep_of_disjoint (ι := ℤ) (E := E) μ
        (S := (sA : Set ℤ)) (T := (sBn : Set ℤ)) hDisj)
  have hIndepSet :
      IndepSet Aε (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε) P :=
    hIndep.indepSet_of_measurableSet hAε_cyl hShiftBε
  have hApproxReal :
      P.real (Aε ∩ (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) =
        P.real Aε * P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) := by
    -- Independence again makes the approximant correlation term exactly zero.
    simpa [Measure.real_def, ENNReal.toReal_mul] using
      congrArg ENNReal.toReal hIndepSet.measure_inter_eq_mul
  have hPreB :
      MeasurableSet (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) :=
    hB.preimage (hPres'.iterate n).measurable
  have hPreBε :
      MeasurableSet (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε) :=
    hBε.preimage (hPres'.iterate n).measurable
  have hPreBReal :
      P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B)) = P.real B := by
    -- Measure preservation identifies the shifted target event with `B`.
    simpa [Measure.real_def] using
      congrArg ENNReal.toReal
        ((hPres'.iterate n).measure_preimage (s := B) hB.nullMeasurableSet)
  have hAε_closeReal : P.real (A ∆ Aε) < δ := by
    simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hAε_close
  have hShiftBε_closeReal :
      P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) ∆
          (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) < δ := by
    have hpre :
        P ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) ∆
            (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) =
          P (B ∆ Bε) := by
      rw [← Set.preimage_symmDiff]
      exact (hPres'.iterate n).measure_preimage (s := B ∆ Bε) (hB.symmDiff hBε).nullMeasurableSet
    rw [show
        P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) ∆
            (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) =
          P.real (B ∆ Bε) by
            simpa [Measure.real_def] using congrArg ENNReal.toReal hpre]
    simpa [Measure.real_def, δ] using ENNReal.toReal_lt_of_lt_ofReal hBε_close
  have hApproxBound :=
    correlationErrorBound_ofApprox (P := P) hA hAε hPreB hPreBε
  -- The bilateral case closes with the same exact-factorization plus `4ε` error estimate.
  calc
    |P.real (A ∩ (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B)) -
        P.real A * P.real B|
        = |P.real (A ∩ (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B)) -
            P.real A *
              P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B))| := by
                rw [hPreBReal]
    _ ≤ |P.real (Aε ∩ (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) -
          P.real Aε *
            P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε))| +
          2 * P.real (A ∆ Aε) +
          2 * P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) ∆
            (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) := by
            simpa [add_assoc, add_left_comm, add_comm] using hApproxBound
    _ = 2 * P.real (A ∆ Aε) +
          2 * P.real ((((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' B) ∆
            (((fun ω : ℤ → E ↦ fun k : ℤ ↦ ω (k + 1))^[n]) ⁻¹' Bε)) := by
              rw [hApproxReal]
              simp
    _ < ε := by
          dsimp [δ] at hAε_closeReal hShiftBε_closeReal ⊢
          nlinarith

-- Proof sketch: strong mixing implies weak mixing, and weak mixing forces the Cesàro averages for
-- an invariant event to be eventually constant; the only possible constant is then `0`, giving
-- the usual `0`-`1` dichotomy.
/-- Any invariant measurable event in a strongly mixing probability-preserving system has
probability `0` or `1`. -/
theorem prob_eq_zero_or_one_of_isStronglyMixing_of_preimage_eq {Ω : Type v}
    [MeasurableSpace Ω] {τ : Ω → Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    (hτ : MeasurePreserving τ P P) (hstrong : IsStronglyMixing τ P) {A : Set Ω}
    (hA : MeasurableSet A) (hτA : τ ⁻¹' A = A) :
    P A = 0 ∨ P A = 1 := by
  -- Keep the measure-preserving hypothesis explicit in the local context: it is part of the
  -- dynamical-system input even though the current closing argument only uses strong mixing.
  let _ := hτ
  have hweak := isWeaklyMixing_of_isStronglyMixing (P := P) hstrong
  let c : ℝ := |P.real A - P.real A * P.real A|
  have hlimit_zero := hweak A A hA hA
  have hlimit_const :
      Tendsto
        (fun n : ℕ ↦
          (1 / (n : ℝ)) *
            (Finset.sum (Finset.range n) fun i ↦
              |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|))
        atTop
        (nhds c) := by
    -- On an invariant event, every correlation term is the same constant.
    refine tendsto_atTop_of_eventually_const (i₀ := 1) ?_
    intro n hn
    have hn0 : (n : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt hn
    have hfixed : Function.IsFixedPt (Set.preimage τ) A := hτA
    have hiterateA : ∀ j : ℕ, (τ^[j]) ⁻¹' A = A := by
      intro j
      exact (Function.IsFixedPt.preimage_iterate (f := τ) hfixed j).eq
    have hsum :
        Finset.sum (Finset.range n) (fun i ↦
          |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
          n * c := by
      calc
        Finset.sum (Finset.range n) (fun i ↦
            |P.real (A ∩ (τ^[i]) ⁻¹' A) - P.real A * P.real A|) =
            Finset.sum (Finset.range n) (fun _ ↦ c) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          rw [hiterateA i]
          simp [c]
        _ = n * c := by
          simp [c]
    -- Rewrite the Cesàro average of the constant sequence.
    rw [hsum]
    field_simp [hn0]
  have hc : c = 0 := tendsto_nhds_unique hlimit_const hlimit_zero
  have hreal : P.real A = 0 ∨ P.real A = 1 := by
    -- Route correction: factor the normalized constant instead of manipulating the original
    -- absolute-value equation directly.
    have hmul : P.real A * (1 - P.real A) = 0 := by
      have habs : P.real A - P.real A * P.real A = 0 := abs_eq_zero.mp hc
      nlinarith
    rcases eq_zero_or_eq_zero_of_mul_eq_zero hmul with hzero | hone
    · exact Or.inl hzero
    · exact Or.inr <| by linarith
  rcases hreal with hzero | hone
  · left
    exact (measureReal_eq_zero_iff (μ := P) (s := A)).mp hzero
  · right
    exact (ENNReal.toReal_eq_one_iff (P A)).mp (by simpa [Measure.real] using hone)
