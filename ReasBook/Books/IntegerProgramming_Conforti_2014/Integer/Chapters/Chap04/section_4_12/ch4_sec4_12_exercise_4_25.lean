/-
Authors: Ziyu Wang, Zaiwen Wen
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@d380aaa277a7a97379616d8bd2809e751c1052f4:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization contributors, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap02.section_2_14.ch2_sec2_14_exercise_2_7
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_6.ch3_sec3_6_definition_3_6_extra_1
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap04.section_4_7.ch4_sec4_7_remark_4_7_extra_2

-- Declarations for this item will be appended below by the statement pipeline.

open scoped BigOperators Matrix

universe u

variable {V : Type u} [DecidableEq V]

/-- A finite family of subsets of `V` is laminar when any two members with nonempty intersection
are nested. -/
def IsLaminarSubsetFamily (𝒮 : Finset (Finset V)) : Prop :=
  ∀ ⦃S T : Finset V⦄, S ∈ 𝒮 → T ∈ 𝒮 → (S ∩ T).Nonempty → S ⊆ T ∨ T ⊆ S

private theorem matrixOfRowSupports_mulVec_apply_local
    {V : Type} [Fintype V] [DecidableEq V]
    (𝒮 : Finset (Finset V)) (x : V → ℝ) (S : 𝒮) :
    ((((matrixOfRowSupports 𝒮 : Matrix 𝒮 V ℤ).map (Int.castRingHom ℝ)) *ᵥ x) S) =
      (S : Finset V).sum x := by
  simp [Matrix.mulVec, dotProduct, matrixOfRowSupports, rowOfSupport]

private theorem matrixOfRowSupports_row_eq_incidence_local
    {V : Type} [DecidableEq V]
    (𝒮 : Finset (Finset V)) (S : 𝒮) :
    ((matrixOfRowSupports 𝒮 : Matrix 𝒮 V ℤ).map (Int.castRingHom ℝ) S) =
      (fun v ↦ if v ∈ (S : Finset V) then (1 : ℝ) else 0) := by
  funext v
  simp [matrixOfRowSupports, rowOfSupport]

/-- Helper for Exercise 4.25: incidence vectors satisfy the standard uncrossing identity. -/
private lemma incidenceVector_inter_union_add {V : Type*} [DecidableEq V] (S T : Finset V) :
    (fun j ↦ if j ∈ S then (1 : ℝ) else 0) + (fun j ↦ if j ∈ T then 1 else 0) =
      (fun j ↦ if j ∈ S ∩ T then (1 : ℝ) else 0) + (fun j ↦ if j ∈ S ∪ T then 1 else 0) := by
  -- Check the four membership cases for each coordinate.
  ext j
  by_cases hS : j ∈ S
  · by_cases hT : j ∈ T
    · simp [hS, hT]
    · simp [hS, hT]
  · by_cases hT : j ∈ T
    · simp [hS, hT]
    · simp [hS, hT]

/-- Helper for Exercise 4.25: the subset sums of `x` satisfy the same intersection-union identity
as the incidence vectors. -/
private lemma sum_inter_add_sum_union {V : Type*} [DecidableEq V]
    (S T : Finset V) (x : V → ℝ) :
    (S ∩ T).sum x + (S ∪ T).sum x = S.sum x + T.sum x := by
  have h_union_eq : S ∪ T = S ∪ (T \ S) := by
    ext j
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [hS, hT]
  have hT_eq : T = (S ∩ T) ∪ (T \ S) := by
    ext j
    by_cases hS : j ∈ S <;> by_cases hT : j ∈ T <;> simp [hS, hT]
  have h_disj_union : Disjoint S (T \ S) := by
    exact Finset.disjoint_left.mpr fun j hj hjs ↦ by
      rw [Finset.mem_sdiff] at hjs
      exact hjs.2 hj
  have h_union : (S ∪ T).sum x = S.sum x + (T \ S).sum x := by
    calc
      (S ∪ T).sum x = (S ∪ (T \ S)).sum x := congrArg (fun U : Finset V ↦ U.sum x) h_union_eq
      _ = S.sum x + (T \ S).sum x := Finset.sum_union h_disj_union
  have h_disj_T : Disjoint (S ∩ T) (T \ S) := by
    exact Finset.disjoint_left.mpr fun j hj hjs ↦ by
      rw [Finset.mem_inter] at hj
      rw [Finset.mem_sdiff] at hjs
      exact hjs.2 hj.1
  have hT : T.sum x = (S ∩ T).sum x + (T \ S).sum x := by
    calc
      T.sum x = ((S ∩ T) ∪ (T \ S)).sum x := congrArg (fun U : Finset V ↦ U.sum x) hT_eq
      _ = (S ∩ T).sum x + (T \ S).sum x := Finset.sum_union h_disj_T
  calc
    (S ∩ T).sum x + (S ∪ T).sum x = (S ∩ T).sum x + (S.sum x + (T \ S).sum x) := by
      rw [h_union]
    _ = S.sum x + ((S ∩ T).sum x + (T \ S).sum x) := by
      simp [add_left_comm]
    _ = S.sum x + T.sum x := by
      rw [hT]

/-- Transport a subset sum along an equivalence of the ground set. -/
private lemma sum_finsetCongr {V W : Type*} (e : V ≃ W) (S : Finset V) (x : W → ℝ) :
    (e.finsetCongr S).sum x = S.sum (x ∘ e) := by
  simpa [Equiv.finsetCongr_apply, Function.comp] using
    (Finset.sum_map S e.toEmbedding x)

/-- Helper for Exercise 4.25: if two subset inequalities are tight at `xbar`, then the
intersection and union inequalities are also tight. -/
lemma tight_inter_union_of_submodular {α : Type} [DecidableEq α]
    (f : Finset α → ℝ)
    (hf_submodular : Submodular f) {xbar : α → ℝ}
    (hxbar_mem : xbar ∈ submodularPolyhedron f) (S T : Finset α)
    (hS : S.sum xbar = f S) (hT : T.sum xbar = f T) :
    (S ∩ T).sum xbar = f (S ∩ T) ∧ (S ∪ T).sum xbar = f (S ∪ T) := by
  -- The point `xbar` satisfies the intersection and union inequalities.
  have hle_inter : (S ∩ T).sum xbar ≤ f (S ∩ T) := hxbar_mem (S ∩ T)
  have hle_union : (S ∪ T).sum xbar ≤ f (S ∪ T) := hxbar_mem (S ∪ T)
  have hsum_sets : (S ∩ T).sum xbar + (S ∪ T).sum xbar = f S + f T := by
    calc
      (S ∩ T).sum xbar + (S ∪ T).sum xbar = S.sum xbar + T.sum xbar := by
        simpa using sum_inter_add_sum_union S T xbar
      _ = f S + f T := by rw [hS, hT]
  have hge_total :
      f (S ∩ T) + f (S ∪ T) ≤ (S ∩ T).sum xbar + (S ∪ T).sum xbar := by
    calc
      f (S ∩ T) + f (S ∪ T) ≤ f S + f T := hf_submodular S T
      _ = (S ∩ T).sum xbar + (S ∪ T).sum xbar := hsum_sets.symm
  have hle_total :
      (S ∩ T).sum xbar + (S ∪ T).sum xbar ≤ f (S ∩ T) + f (S ∪ T) := by
    exact add_le_add hle_inter hle_union
  have htotal :
      (S ∩ T).sum xbar + (S ∪ T).sum xbar = f (S ∩ T) + f (S ∪ T) := by
    exact le_antisymm hle_total hge_total
  have h_inter : (S ∩ T).sum xbar = f (S ∩ T) := by
    linarith
  have h_union : (S ∪ T).sum xbar = f (S ∪ T) := by
    linarith
  exact ⟨h_inter, h_union⟩

/-- Helper for Exercise 4.25: an extreme point of `polyhedron_le_set A b` admits `n` active rows
whose coefficient vectors are linearly independent. -/
private lemma exists_active_linearlyIndependent_rows_of_extremePoint {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) {xbar : Fin n → ℝ}
    (hxbar : xbar ∈ polyhedron_le_set A b)
    (hxbar_vertex : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ) :
    ∃ I : Fin n ↪ Fin m,
      (∀ i : Fin n, (A *ᵥ xbar) (I i) = b (I i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ A (I i)) := by
  classical
  let activeRows : Set (Fin n → ℝ) :=
    Set.range fun i : {i // (A *ᵥ xbar) i = b i} ↦ A i.1
  have hspan : Submodule.span ℝ activeRows = ⊤ := by
    by_contra hspan_ne
    let K : Submodule ℝ (Fin n → ℝ) := Submodule.span ℝ activeRows
    have hKlt : K < ⊤ := lt_of_le_of_ne le_top hspan_ne
    obtain ⟨φ, hφ_ne, hKker⟩ := Submodule.exists_le_ker_of_lt_top K hKlt
    let r : Fin n → ℝ := (dotProductEquiv ℝ (Fin n)).symm φ
    have hr_ne : r ≠ 0 := by
      intro hr
      apply hφ_ne
      simpa [r, hr] using ((dotProductEquiv ℝ (Fin n)).apply_symm_apply φ).symm
    have hactive_eval : ∀ i : Fin m, (A *ᵥ xbar) i = b i → (A *ᵥ r) i = 0 := by
      intro i hi
      have hAi_mem : A i ∈ K := by
        refine Submodule.subset_span ?_
        exact ⟨⟨i, hi⟩, rfl⟩
      have hφAi : φ (A i) = 0 := by
        simpa using hKker hAi_mem
      have hφr : (dotProductEquiv ℝ (Fin n)) r = φ := by
        simp [r]
      have hdot : dotProduct r (A i) = 0 := by
        simpa [hφAi] using congrArg (fun f : Module.Dual ℝ (Fin n → ℝ) => f (A i)) hφr
      have hrowdot : dotProduct (A i) r = 0 := by
        simpa [dotProduct_comm] using hdot
      simpa [Matrix.mulVec, dotProduct] using hrowdot
    let δ : Fin m → ℝ := fun i ↦
      if hi : (A *ᵥ xbar) i = b i then 1
      else if hzero : (A *ᵥ r) i = 0 then 1
      else (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|
    have hδ_pos : ∀ i : Fin m, 0 < δ i := by
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · simp [δ, hi]
      · by_cases hzero : (A *ᵥ r) i = 0
        · simp [δ, hi, hzero]
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hnum : 0 < b i - (A *ᵥ xbar) i := sub_pos.mpr hlt
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          simp [δ, hi, hzero, div_pos hnum hden]
    let δs : Finset ℝ := insert 1 (Finset.univ.image δ)
    let ε : ℝ := δs.min' (by simp [δs]) / 2
    have hmin_pos : 0 < δs.min' (by simp [δs]) := by
      have hmin_mem : δs.min' (by simp [δs]) ∈ δs := Finset.min'_mem _ _
      rcases Finset.mem_insert.mp hmin_mem with h1 | himage
      · simpa [h1]
      · rcases Finset.mem_image.mp himage with ⟨i, _, hi⟩
        rw [← hi]
        exact hδ_pos i
    have hε_pos : 0 < ε := half_pos hmin_pos
    have hε_le : ∀ i : Fin m, ε ≤ δ i := by
      intro i
      have hmin_le : δs.min' (by simp [δs]) ≤ δ i := by
        apply Finset.min'_le
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
      have hhalf_le : δs.min' (by simp [δs]) / 2 ≤ δs.min' (by simp [δs]) := by
        linarith
      exact hhalf_le.trans hmin_le
    have hperturb_eval (σ : ℝ) (i : Fin m) :
        (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := by
      rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      simp
    have hperturb_mem : ∀ {σ : ℝ}, |σ| ≤ ε → xbar + σ • r ∈ polyhedron_le_set A b := by
      intro σ hσ
      rw [mem_polyhedron_le_set_iff]
      intro i
      by_cases hi : (A *ᵥ xbar) i = b i
      · calc
          (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
          _ = b i := by simp [hi, hactive_eval i hi]
          _ ≤ b i := le_rfl
      · by_cases hzero : (A *ᵥ r) i = 0
        · calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ = (A *ᵥ xbar) i := by simp [hzero]
            _ ≤ b i := hxbar i
        · have hlt : (A *ᵥ xbar) i < b i := lt_of_le_of_ne (hxbar i) hi
          have hσ_bound : |σ| ≤ (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by
            calc
              |σ| ≤ ε := hσ
              _ ≤ δ i := hε_le i
              _ = (b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i| := by simp [δ, hi, hzero]
          have hden : 0 < |(A *ᵥ r) i| := abs_pos.mpr hzero
          have hmul_le :
              |σ| * |(A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            have hmul := mul_le_mul_of_nonneg_right hσ_bound hden.le
            have hcancel :
                ((b i - (A *ᵥ xbar) i) / |(A *ᵥ r) i|) * |(A *ᵥ r) i| =
                  b i - (A *ᵥ xbar) i := by
              field_simp [hden.ne']
            simpa [hcancel] using hmul
          have habs_le : |σ * (A *ᵥ r) i| ≤ b i - (A *ᵥ xbar) i := by
            simpa [abs_mul] using hmul_le
          have hterm_le : σ * (A *ᵥ r) i ≤ b i - (A *ᵥ xbar) i := by
            exact (le_abs_self _).trans habs_le
          calc
            (A *ᵥ (xbar + σ • r)) i = (A *ᵥ xbar) i + σ * (A *ᵥ r) i := hperturb_eval σ i
            _ ≤ b i := by linarith
    let xMinus : Fin n → ℝ := xbar - ε • r
    let xPlus : Fin n → ℝ := xbar + ε • r
    have hxMinus : xMinus ∈ polyhedron_le_set A b := by
      have hneg : |(-ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xMinus, sub_eq_add_neg] using (hperturb_mem (σ := -ε) hneg)
    have hxPlus : xPlus ∈ polyhedron_le_set A b := by
      have hpos : |(ε : ℝ)| ≤ ε := by simpa [abs_of_nonneg hε_pos.le]
      simpa [xPlus] using (hperturb_mem (σ := ε) hpos)
    have hxMinus_ne : xMinus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := sub_eq_self.mp hEq
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxPlus_ne : xPlus ≠ xbar := by
      intro hEq
      have hsmul : ε • r = 0 := by
        have := congrArg (fun u : Fin n → ℝ ↦ u - xbar) hEq
        simpa [xPlus, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      exact hr_ne ((smul_eq_zero.mp hsmul).resolve_left (ne_of_gt hε_pos))
    have hxbar_segment : xbar ∈ segment ℝ xMinus xPlus := by
      simpa [xMinus, xPlus] using (mem_segment_sub_add (𝕜 := ℝ) xbar (ε • r))
    have hxbar_open : xbar ∈ openSegment ℝ xMinus xPlus := by
      exact mem_openSegment_of_ne_left_right hxMinus_ne hxPlus_ne hxbar_segment
    have hxext := (mem_extremePoints_iff_left).mp hxbar_vertex
    exact hxMinus_ne (hxext.2 xMinus hxMinus xPlus hxPlus hxbar_open)
  have hdim : Module.finrank ℝ ↥(Submodule.span ℝ activeRows) = n := by
    rw [hspan]
    simpa using (Module.finrank_fin_fun ℝ (n := n))
  obtain ⟨g, hg_mem, _hg_span, hg_linear⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ activeRows
  let e : Fin (Module.finrank ℝ ↥(Submodule.span ℝ activeRows)) ≃ Fin n :=
    (Fin.castOrderIso hdim).toEquiv
  let rows : Fin n → Fin n → ℝ := fun i ↦ g (e.symm i)
  have hrows_mem : ∀ i : Fin n, rows i ∈ activeRows := by
    intro i
    exact hg_mem (e.symm i)
  have hrows_linear : LinearIndependent ℝ rows := by
    exact (linearIndependent_equiv e.symm).2 hg_linear
  have hrows_mem' :
      ∀ i : Fin n, ∃ j : {j // (A *ᵥ xbar) j = b j}, A j.1 = rows i := by
    intro i
    simpa [activeRows] using hrows_mem i
  let chosen : Fin n → {j // (A *ᵥ xbar) j = b j} :=
    fun i ↦ Classical.choose (hrows_mem' i)
  have hchosen_row : ∀ i : Fin n, A (chosen i).1 = rows i := by
    intro i
    exact Classical.choose_spec (hrows_mem' i)
  have hchosen_injective : Function.Injective fun i : Fin n ↦ (chosen i).1 := by
    intro i j hij
    apply hrows_linear.injective
    calc
      rows i = A (chosen i).1 := (hchosen_row i).symm
      _ = A (chosen j).1 := by simpa [hij]
      _ = rows j := hchosen_row j
  let I : Fin n ↪ Fin m := ⟨fun i ↦ (chosen i).1, hchosen_injective⟩
  refine ⟨I, ?_, ?_⟩
  · intro i
    exact (chosen i).2
  · have hrows : (fun i : Fin n ↦ A (I i)) = rows := by
      funext i
      exact hchosen_row i
    simpa [hrows] using hrows_linear

/-- Internal `Fin`-indexed bridge for extracting an active basis from the matrix presentation. -/
private lemma exists_active_independent_family_of_vertex_fin {n : ℕ} (f : Finset (Fin n) → ℝ)
    {xbar : Fin n → ℝ} (hxbar_vertex : xbar ∈ (submodularPolyhedron f).extremePoints ℝ) :
    ∃ T : Fin n → Finset (Fin n),
      (∀ i : Fin n, (T i).sum xbar = f (T i)) ∧
        LinearIndependent ℝ (fun i : Fin n ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0) := by
  classical
  let m : ℕ := Fintype.card (Finset (Fin n))
  let e : Fin m ≃ Finset (Fin n) := (Fintype.equivFin (Finset (Fin n))).symm
  let 𝒮 : Finset (Finset (Fin n)) := Finset.univ.image e
  have he_mem : ∀ i : Fin m, e i ∈ 𝒮 := by
    intro i
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  let A : Matrix (Fin m) (Fin n) ℝ := fun i ↦
    ((matrixOfRowSupports 𝒮 : Matrix 𝒮 (Fin n) ℤ).map (Int.castRingHom ℝ) ⟨e i, he_mem i⟩)
  let b : Fin m → ℝ := fun i ↦ f (e i)
  have hA_mulVec (x : Fin n → ℝ) (i : Fin m) : (A *ᵥ x) i = (e i).sum x := by
    simpa [A] using matrixOfRowSupports_mulVec_apply_local 𝒮 x ⟨e i, he_mem i⟩
  have hpoly :
      submodularPolyhedron f = polyhedron_le_set A b := by
    ext x
    constructor
    · intro hx
      rw [mem_submodularPolyhedron_iff] at hx
      rw [mem_polyhedron_le_set_iff]
      intro i
      simpa [b, hA_mulVec x i] using hx (e i)
    · intro hx
      rw [mem_polyhedron_le_set_iff] at hx
      intro S
      obtain ⟨i, rfl⟩ := e.surjective S
      simpa [b, hA_mulVec x i] using hx i
  have hxbar_polyhedron : xbar ∈ polyhedron_le_set A b := by
    -- An extreme point belongs to the polyhedron itself.
    simpa [hpoly] using extremePoints_subset hxbar_vertex
  have hxbar_vertex_matrix : xbar ∈ (polyhedron_le_set A b).extremePoints ℝ := by
    -- Rewrite the extreme-point hypothesis through the matrix presentation.
    simpa [hpoly] using hxbar_vertex
  obtain ⟨I, hactive, hlinear⟩ :=
    exists_active_linearlyIndependent_rows_of_extremePoint A b hxbar_polyhedron
      hxbar_vertex_matrix
  refine ⟨fun i ↦ e (I i), ?_⟩
  constructor
  · intro i
    simpa [b, hA_mulVec xbar (I i)] using hactive i
  · have hrows :
        (fun i : Fin n ↦ A (I i)) =
          (fun i : Fin n ↦ fun j ↦ if j ∈ e (I i) then (1 : ℝ) else 0) := by
      funext i
      simpa [A] using matrixOfRowSupports_row_eq_incidence_local 𝒮 ⟨e (I i), he_mem (I i)⟩
    simpa [hrows] using hlinear

/-- Helper for Exercise 4.25: a vertex yields `|α|` active subset inequalities with linearly
independent incidence vectors. -/
lemma exists_active_independent_family_of_vertex {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) {xbar : α → ℝ}
    (hxbar_vertex : xbar ∈ (submodularPolyhedron f).extremePoints ℝ) :
    ∃ T : α → Finset α,
      (∀ i : α, (T i).sum xbar = f (T i)) ∧
        LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0) := by
  classical
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let L : (α → ℝ) ≃ₗ[ℝ] Fin (Fintype.card α) → ℝ := LinearEquiv.funCongrLeft ℝ ℝ e
  let fFin : Finset (Fin (Fintype.card α)) → ℝ := f ∘ e.finsetCongr
  have hmem_congr (x : α → ℝ) : L x ∈ submodularPolyhedron fFin ↔ x ∈ submodularPolyhedron f := by
    rw [mem_submodularPolyhedron_iff, mem_submodularPolyhedron_iff]
    constructor
    · intro hx T
      have hcongr : Finset.map e.toEmbedding (Finset.map e.symm.toEmbedding T) = T := by
        ext a
        simp
      simpa [fFin, L, LinearEquiv.funCongrLeft_apply, sum_finsetCongr,
        Equiv.finsetCongr_apply, hcongr] using
        hx (e.finsetCongr.symm T)
    · intro hx S
      simpa [fFin, L, LinearEquiv.funCongrLeft_apply, sum_finsetCongr] using hx (e.finsetCongr S)
  have himage :
      L '' submodularPolyhedron f = submodularPolyhedron fFin := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hmem_congr x).2 hx
    · intro hy
      refine ⟨L.symm y, ?_, ?_⟩
      · exact (hmem_congr (L.symm y)).1 (by
          convert hy using 1
          ext i
          simp [L])
      · ext i
        simp [L]
  have hxbar_vertex_fin : L xbar ∈ (submodularPolyhedron fFin).extremePoints ℝ := by
    have himage_extreme :
        L '' (submodularPolyhedron f).extremePoints ℝ =
          (submodularPolyhedron fFin).extremePoints ℝ := by
      rw [image_extremePoints, himage]
    rw [← himage_extreme]
    exact ⟨xbar, hxbar_vertex, rfl⟩
  obtain ⟨TFin, hactiveFin, hlinearFin⟩ :=
    exists_active_independent_family_of_vertex_fin fFin hxbar_vertex_fin
  let T : α → Finset α := fun i ↦ e.finsetCongr (TFin (Fintype.equivFin α i))
  refine ⟨T, ?_⟩
  constructor
  · intro i
    simpa [T, fFin, L, LinearEquiv.funCongrLeft_apply, sum_finsetCongr] using
      hactiveFin (Fintype.equivFin α i)
  · have hlinearMapped :
        LinearIndependent ℝ
          (L.symm.toLinearMap ∘
            (fun i : Fin (Fintype.card α) ↦ fun j ↦ if j ∈ TFin i then (1 : ℝ) else 0)) := by
      simpa using hlinearFin.map' L.symm.toLinearMap (by simp)
    have hlinearReindexed :
        LinearIndependent ℝ
          (fun i : α ↦
            L.symm (fun j ↦ if j ∈ TFin (Fintype.equivFin α i) then (1 : ℝ) else 0)) := by
      exact (linearIndependent_equiv (Fintype.equivFin α)).2 hlinearMapped
    have hT :
        (fun i : α ↦ L.symm (fun j ↦ if j ∈ TFin (Fintype.equivFin α i) then (1 : ℝ) else 0)) =
          (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0) := by
      funext i j
      simp [T, L, LinearEquiv.funCongrLeft_apply, Equiv.finsetCongr_apply, Finset.mem_map_equiv]
    simpa [hT] using hlinearReindexed

/-- Helper for Exercise 4.25: the supporting objective obtained by summing the active incidence
rows. -/
private def activeFamilyObjective {α : Type*} [Fintype α] [DecidableEq α]
    (T : α → Finset α) : α → ℝ :=
  fun j ↦ ∑ i, if j ∈ T i then (1 : ℝ) else 0

/-- Helper for Exercise 4.25: the row-sum objective is the sum of the active subset sums. -/
private lemma dot_activeFamilyObjective_eq_sum_activeSums
    {α : Type*} [Fintype α] [DecidableEq α]
    (T : α → Finset α) (x : α → ℝ) :
    activeFamilyObjective T ⬝ᵥ x = ∑ i, (T i).sum x := by
  calc
    activeFamilyObjective T ⬝ᵥ x
        = ∑ j, (∑ i, if j ∈ T i then (1 : ℝ) else 0) * x j := by
            simp [activeFamilyObjective, dotProduct]
    _ = ∑ j, ∑ i, (if j ∈ T i then (1 : ℝ) else 0) * x j := by
          refine Finset.sum_congr rfl ?_
          intro j hj
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ j, (if j ∈ T i then (1 : ℝ) else 0) * x j := by
          rw [Finset.sum_comm]
    _ = ∑ i, (T i).sum x := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          simp

/-- Helper for Exercise 4.25: if two points satisfy the same equalities on an active independent
family, then they coincide. -/
private lemma dot_eq_zero_of_mem_span
    {α : Type} [Fintype α] [DecidableEq α]
    {v : α → α → ℝ} {d w : α → ℝ}
    (hdot : ∀ i : α, v i ⬝ᵥ d = 0)
    (hw : w ∈ Submodule.span ℝ (Set.range v)) :
    w ⬝ᵥ d = 0 := by
  let Z : Submodule ℝ (α → ℝ) :=
    { carrier := {z | z ⬝ᵥ d = 0}
      zero_mem' := by
        simp [dotProduct]
      add_mem' := by
        intro x y hx hy
        have hx0 : x ⬝ᵥ d = 0 := by simpa using hx
        have hy0 : y ⬝ᵥ d = 0 := by simpa using hy
        change (x + y) ⬝ᵥ d = 0
        rw [add_dotProduct, hx0, hy0]
        simp
      smul_mem' := by
        intro a z hz
        have hz0 : z ⬝ᵥ d = 0 := by simpa using hz
        change (a • z) ⬝ᵥ d = 0
        rw [smul_dotProduct, hz0]
        simp }
  have hrange : Set.range v ⊆ (Z : Set (α → ℝ)) := by
    intro z hz
    rcases hz with ⟨i, rfl⟩
    exact hdot i
  have hspan_le : Submodule.span ℝ (Set.range v) ≤ Z := Submodule.span_le.mpr hrange
  exact hspan_le hw

private lemma eq_of_eq_activeSums_of_linearIndependent
    {α : Type} [Fintype α] [DecidableEq α]
    {T : α → Finset α}
    (hlinear :
      LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0))
    {x y : α → ℝ}
    (hxy : ∀ i : α, (T i).sum x = (T i).sum y) :
    x = y := by
  classical
  let v : α → α → ℝ := fun i j ↦ if j ∈ T i then (1 : ℝ) else 0
  have hv : LinearIndependent ℝ v := by
    simpa [v] using hlinear
  have hspan : Submodule.span ℝ (Set.range v) = ⊤ := by
    refine hv.span_eq_top_of_card_eq_finrank' ?_
    simp [Module.finrank_fintype_fun_eq_card]
  have hdot_zero : ∀ i : α, v i ⬝ᵥ (x - y) = 0 := by
    intro i
    calc
      v i ⬝ᵥ (x - y)
          = Finset.sum (T i) (fun j ↦ x j - y j) := by
              simp [v, dotProduct]
      _ = (T i).sum x - (T i).sum y := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := sub_eq_zero.mpr (hxy i)
  ext j
  have hsingle : (Pi.single j (1 : ℝ) : α → ℝ) ∈ Submodule.span ℝ (Set.range v) := by
    rw [hspan]
    simp
  have hj_zero : (Pi.single j (1 : ℝ) : α → ℝ) ⬝ᵥ (x - y) = 0 :=
    dot_eq_zero_of_mem_span hdot_zero hsingle
  have hj_eq : x j - y j = 0 := by
    simpa using (single_one_dotProduct j (x - y)).symm.trans hj_zero
  exact sub_eq_zero.mp hj_eq

/-- Helper for Exercise 4.25: the row-sum objective exposes `xbar` uniquely among feasible points
once the active rows are linearly independent. -/
private lemma activeFamilyObjective_supports_and_uniquely_exposes
    {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) {xbar : α → ℝ}
    (hxbar_mem : xbar ∈ submodularPolyhedron f) {T : α → Finset α}
    (hactive : ∀ i : α, (T i).sum xbar = f (T i))
    (hlinear :
      LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0)) :
    (∀ x : α → ℝ,
        x ∈ submodularPolyhedron f →
          activeFamilyObjective T ⬝ᵥ x ≤ activeFamilyObjective T ⬝ᵥ xbar) ∧
      (∀ x : α → ℝ,
        x ∈ submodularPolyhedron f →
          activeFamilyObjective T ⬝ᵥ x = activeFamilyObjective T ⬝ᵥ xbar →
            x = xbar) := by
  constructor
  · intro x hx
    -- Sum the defining subset inequalities over the active family.
    calc
      activeFamilyObjective T ⬝ᵥ x = ∑ i, (T i).sum x := by
        simpa using dot_activeFamilyObjective_eq_sum_activeSums T x
      _ ≤ ∑ i, f (T i) := by
        exact Finset.sum_le_sum fun i hi ↦ hx (T i)
      _ = ∑ i, (T i).sum xbar := by
        refine Finset.sum_congr rfl ?_
        intro i hi
        exact (hactive i).symm
      _ = activeFamilyObjective T ⬝ᵥ xbar := by
        simpa using (dot_activeFamilyObjective_eq_sum_activeSums T xbar).symm
  · intro x hx hx_eq
    have hsum_eq :
        ∑ i, f (T i) = ∑ i, (T i).sum x := by
      calc
        ∑ i, f (T i) = activeFamilyObjective T ⬝ᵥ xbar := by
          rw [dot_activeFamilyObjective_eq_sum_activeSums T xbar]
          refine Finset.sum_congr rfl ?_
          intro i hi
          exact (hactive i).symm
        _ = activeFamilyObjective T ⬝ᵥ x := hx_eq.symm
        _ = ∑ i, (T i).sum x := dot_activeFamilyObjective_eq_sum_activeSums T x
    have hrow_eq : ∀ i : α, (T i).sum x = f (T i) := by
      intro i
      have hle_row : (T i).sum x ≤ f (T i) := hx (T i)
      have hsum_zero : ∑ j, (f (T j) - (T j).sum x) = 0 := by
        calc
          ∑ j, (f (T j) - (T j).sum x) = ∑ j, f (T j) - ∑ j, (T j).sum x := by
            rw [Finset.sum_sub_distrib]
          _ = 0 := by
            linarith [hsum_eq]
      have hzero_all : ∀ j, f (T j) - (T j).sum x = 0 := by
        have hnonneg : ∀ j ∈ Finset.univ, 0 ≤ f (T j) - (T j).sum x := by
          intro j hj
          exact sub_nonneg.mpr (hx (T j))
        simpa using (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum_zero
      have hcurrent_ge : f (T i) ≤ (T i).sum x := by
        linarith [hzero_all i]
      exact le_antisymm hle_row hcurrent_ge
    have hxbar_rows : ∀ i : α, (T i).sum x = (T i).sum xbar := by
      intro i
      rw [hrow_eq i, hactive i]
    exact eq_of_eq_activeSums_of_linearIndependent hlinear hxbar_rows

/-- Helper for Exercise 4.25: package the explicit row-sum objective as the exposing objective
used later in the greedy transport. -/
private lemma exists_supportingObjective_with_uniqueMaximizer_of_activeIndependentFamily
    {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) {xbar : α → ℝ}
    (hxbar_mem : xbar ∈ submodularPolyhedron f) {T : α → Finset α}
    (hactive : ∀ i : α, (T i).sum xbar = f (T i))
    (hlinear :
      LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0)) :
    ∃ c : α → ℝ,
      (∀ x : α → ℝ, x ∈ submodularPolyhedron f → c ⬝ᵥ x ≤ c ⬝ᵥ xbar) ∧
        (∀ x : α → ℝ, x ∈ submodularPolyhedron f → c ⬝ᵥ x = c ⬝ᵥ xbar → x = xbar) := by
  refine ⟨activeFamilyObjective T, ?_⟩
  exact activeFamilyObjective_supports_and_uniquely_exposes f hxbar_mem hactive hlinear

/-- Helper for Exercise 4.25: relabel a finite subset along an equivalence of the ground set. -/
private def relabelFinset {γ β : Type*} [DecidableEq β] (e : γ ≃ β) (S : Finset γ) : Finset β :=
  S.map e.toEmbedding

/-- Helper for Exercise 4.25: membership in a relabeled finite subset is transported by the
inverse equivalence. -/
@[simp] private theorem mem_relabelFinset {γ β : Type*} [DecidableEq β]
    (e : γ ≃ β) {S : Finset γ} {b : β} :
    b ∈ relabelFinset e S ↔ e.symm b ∈ S := by
  simp [relabelFinset]

/-- Helper for Exercise 4.25: relabeling preserves intersections of finite subsets. -/
@[simp] private theorem relabelFinset_inter {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S T : Finset γ) :
    relabelFinset e (S ∩ T) = relabelFinset e S ∩ relabelFinset e T := by
  ext b
  simp [Finset.mem_inter]

/-- Helper for Exercise 4.25: relabeling preserves unions of finite subsets. -/
@[simp] private theorem relabelFinset_union {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S T : Finset γ) :
    relabelFinset e (S ∪ T) = relabelFinset e S ∪ relabelFinset e T := by
  ext b
  simp [Finset.mem_union]

/-- Helper for Exercise 4.25: relabeling by an equivalence and then back by the inverse restores
the original subset. -/
@[simp] private theorem relabelFinset_relabelFinset {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (S : Finset γ) :
    relabelFinset e.symm (relabelFinset e S) = S := by
  ext a
  simp

/-- Helper for Exercise 4.25: summing over a relabeled subset is the same as composing the summand
with the relabeling equivalence. -/
private lemma sum_relabelFinset {γ β : Type*} [DecidableEq β]
    (e : γ ≃ β) (x : β → ℝ) (S : Finset γ) :
    Finset.sum (relabelFinset e S) x = Finset.sum S (fun a ↦ x (e a)) := by
  simpa [relabelFinset] using Finset.sum_map (f := x) e.toEmbedding S

/-- Helper for Exercise 4.25: the working normalization changes only the empty-set value. -/
private def normalizeEmpty {α : Type*} [DecidableEq α] (f : Finset α → ℝ) : Finset α → ℝ :=
  fun S ↦ if S = ∅ then 0 else f S

/-- Helper for Exercise 4.25: the normalization sets the empty-set value to `0`. -/
@[simp] private lemma normalizeEmpty_empty {α : Type*} [DecidableEq α] (f : Finset α → ℝ) :
    normalizeEmpty f ∅ = 0 := by
  simp [normalizeEmpty]

/-- Helper for Exercise 4.25: the normalization agrees with the original function on nonempty
subsets. -/
private lemma normalizeEmpty_of_ne_empty {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) {S : Finset α}
    (hS : S ≠ ∅) :
    normalizeEmpty f S = f S := by
  simp [normalizeEmpty, hS]

/-- Helper for Exercise 4.25: if `f ∅` is nonnegative, changing only the empty-set value preserves
submodularity. -/
private lemma submodular_normalizeEmpty {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f) (hEmptyNonneg : 0 ≤ f ∅) :
    Submodular (normalizeEmpty f) := by
  intro S T
  by_cases hS : S = ∅
  · subst hS
    simp [normalizeEmpty, hEmptyNonneg]
  by_cases hT : T = ∅
  · subst hT
    simp [normalizeEmpty, hEmptyNonneg]
  by_cases hI : S ∩ T = ∅
  · have hsub : f (S ∩ T) + f (S ∪ T) ≤ f S + f T := hf S T
    have hzero : 0 ≤ f (S ∩ T) := by
      simpa [hI] using hEmptyNonneg
    have hmain : f (S ∪ T) ≤ f S + f T := by
      linarith
    simpa [normalizeEmpty, hS, hT, hI] using hmain
  · simpa [normalizeEmpty, hS, hT, hI] using hf S T

/-- Helper for Exercise 4.25: if `f ∅` is nonnegative, changing only the empty-set value does not
change the submodular polyhedron. -/
private lemma mem_submodularPolyhedron_normalizeEmpty_iff {α : Type*}
    [DecidableEq α]
    (f : Finset α → ℝ) (hEmptyNonneg : 0 ≤ f ∅) {x : α → ℝ} :
    x ∈ submodularPolyhedron (normalizeEmpty f) ↔ x ∈ submodularPolyhedron f := by
  rw [mem_submodularPolyhedron_iff, mem_submodularPolyhedron_iff]
  constructor
  · intro hx S
    by_cases hS : S = ∅
    · subst hS
      simpa using hEmptyNonneg
    · simpa [normalizeEmpty, hS] using hx S
  · intro hx S
    by_cases hS : S = ∅
    · subst hS
      simp [normalizeEmpty]
    · simpa [normalizeEmpty, hS] using hx S

/-- Helper for Exercise 4.25: relabeling the ground set preserves submodularity. -/
private lemma submodular_relabelFinset {γ β : Type*} [DecidableEq γ] [DecidableEq β]
    (e : γ ≃ β) (f : Finset γ → ℝ) (hf : Submodular f) :
    Submodular (fun S : Finset β ↦ f (relabelFinset e.symm S)) := by
  intro S T
  simpa using hf (relabelFinset e.symm S) (relabelFinset e.symm T)

/-- Helper for Exercise 4.25: diminishing returns along nested subsets is the single submodularity
fact used in the greedy feasibility proof. -/
private lemma submodularMarginal_le_of_subset {α : Type*} [DecidableEq α]
    (f : Finset α → ℝ) (hf : Submodular f)
    {A B : Finset α} (hAB : A ⊆ B) {e : α} (he : e ∉ B) :
    f (insert e B) - f B ≤ f (insert e A) - f A := by
  have heA : e ∉ A := fun h ↦ he (hAB h)
  have h_inter : insert e A ∩ B = A := by
    ext x
    by_cases hx : x = e
    · subst hx
      simp [he, heA]
    · constructor
      · intro hxmem
        simp [Finset.mem_inter, Finset.mem_insert, hx] at hxmem
        exact hxmem.1
      · intro hxA
        simp [Finset.mem_inter, Finset.mem_insert, hx, hxA, hAB hxA]
  have h_union : insert e A ∪ B = insert e B := by
    ext x
    by_cases hx : x = e
    · subst hx
      simp
    · constructor
      · intro hxmem
        rcases Finset.mem_union.mp hxmem with hxA | hxB
        · have hxA' : x ∈ A := by
            simpa [Finset.mem_insert, hx] using hxA
          simp [Finset.mem_insert, hx, hAB hxA']
        · simp [Finset.mem_insert, hx, hxB]
      · intro hxmem
        rcases Finset.mem_insert.mp hxmem with hxE | hxB
        · exact False.elim (hx hxE)
        · exact Finset.mem_union.mpr (Or.inr hxB)
  have hsub : f A + f (insert e B) ≤ f (insert e A) + f B := by
    simpa [h_inter, h_union] using hf (insert e A) B
  linarith

/-- Helper for Exercise 4.25: the sorted identity-order greedy prefixes form a laminar family. -/
private lemma isLaminarSubsetFamily_image_submodularGreedyPrefix (n : ℕ) :
    IsLaminarSubsetFamily
      (Finset.univ.image fun r : Fin n ↦ submodularGreedyPrefix n (r.1 + 1)) := by
  intro S T hS hT hST
  rcases Finset.mem_image.1 hS with ⟨r, -, rfl⟩
  rcases Finset.mem_image.1 hT with ⟨s, -, rfl⟩
  by_cases hrs : r.1 ≤ s.1
  · left
    intro j hj
    rw [mem_submodularGreedyPrefix_iff] at hj ⊢
    omega
  · right
    intro j hj
    rw [mem_submodularGreedyPrefix_iff] at hj ⊢
    omega

/-- Helper for Exercise 4.25: each greedy prefix is obtained from the previous one by inserting
the new right-endpoint. -/
private lemma submodularGreedyPrefix_succ_eq_insert {n : ℕ} (i : Fin n) :
    submodularGreedyPrefix n (i.1 + 1) = insert i (submodularGreedyPrefix n i.1) := by
  -- Compare membership coordinatewise and isolate the new endpoint `i`.
  ext j
  constructor
  · intro hj
    by_cases hji : j = i
    · simp [hji]
    · apply Finset.mem_insert.mpr
      right
      rw [mem_submodularGreedyPrefix_iff] at hj ⊢
      have hval : j.1 ≠ i.1 := fun h ↦ hji (Fin.ext h)
      omega
  · intro hj
    rcases Finset.mem_insert.1 hj with rfl | hj'
    · simp [mem_submodularGreedyPrefix_iff]
    · rw [mem_submodularGreedyPrefix_iff] at hj' ⊢
      omega

/-- Helper for Exercise 4.25: the real-valued greedy increments telescope exactly on every
identity-order prefix. -/
private lemma greedyPrefixSum_eq_prefixValue {n : ℕ} (f : Finset (Fin n) → ℝ)
    (h_empty : f ∅ = 0) :
    ∀ r : ℕ, ∀ hr : r ≤ n,
      Finset.sum (submodularGreedyPrefix n r)
        (fun i ↦ f (submodularGreedyPrefix n (i.1 + 1)) - f (submodularGreedyPrefix n i.1)) =
          f (submodularGreedyPrefix n r) := by
  intro r hr
  induction' r with r ihr
  · -- The empty prefix contributes no increment, so the telescoping starts from `f ∅ = 0`.
    simp [submodularGreedyPrefix, h_empty]
  · have hrlt : r < n := Nat.lt_of_lt_of_le (Nat.lt_succ_self r) hr
    let i : Fin n := ⟨r, hrlt⟩
    have hprefix :
        submodularGreedyPrefix n (r + 1) = insert i (submodularGreedyPrefix n r) := by
      simpa [i] using submodularGreedyPrefix_succ_eq_insert i
    have hi_not_mem : i ∉ submodularGreedyPrefix n r := by
      rw [mem_submodularGreedyPrefix_iff]
      exact lt_irrefl r
    -- Peel off the new endpoint and use the induction hypothesis on the shorter prefix.
    calc
      Finset.sum (submodularGreedyPrefix n (r + 1))
          (fun j ↦ f (submodularGreedyPrefix n (j.1 + 1)) - f (submodularGreedyPrefix n j.1))
          =
          (f (submodularGreedyPrefix n (r + 1)) - f (submodularGreedyPrefix n r)) +
            Finset.sum (submodularGreedyPrefix n r)
              (fun j ↦ f (submodularGreedyPrefix n (j.1 + 1)) - f (submodularGreedyPrefix n j.1)) := by
            rw [hprefix, Finset.sum_insert hi_not_mem]
            simpa [i, hprefix]
      _ = (f (submodularGreedyPrefix n (r + 1)) - f (submodularGreedyPrefix n r)) +
            f (submodularGreedyPrefix n r) := by
            rw [ihr (Nat.le_of_succ_le hr)]
      _ = f (submodularGreedyPrefix n (r + 1)) := by
            ring

/-- Helper for Exercise 4.25: one greedy increment is bounded by the restricted marginal over any
subset below the current coordinate. -/
private lemma greedyCoordinate_le_restrictedMarginal {n : ℕ}
    (f : Finset (Fin n) → ℝ) (hf : Submodular f)
    (S : Finset (Fin n)) (i : Fin n) :
    f (submodularGreedyPrefix n (i.1 + 1)) - f (submodularGreedyPrefix n i.1) ≤
      f (insert i (S.filter fun j ↦ j.1 < i.1)) - f (S.filter fun j ↦ j.1 < i.1) := by
  let Slt : Finset (Fin n) := S.filter fun j ↦ j.1 < i.1
  have hSlt_subset : Slt ⊆ submodularGreedyPrefix n i.1 := by
    intro j hj
    rw [mem_submodularGreedyPrefix_iff]
    exact (Finset.mem_filter.1 hj).2
  have hi_not_mem : i ∉ submodularGreedyPrefix n i.1 := by
    rw [mem_submodularGreedyPrefix_iff]
    exact lt_irrefl i.1
  -- Apply diminishing returns once between the sorted prefix and the restricted subset.
  simpa [Slt, submodularGreedyPrefix_succ_eq_insert] using
    submodularMarginal_le_of_subset f hf hSlt_subset hi_not_mem

/-- Helper for Exercise 4.25: erasing the maximum element of a nonempty finite subset of `Fin n`
leaves exactly the elements whose values are strictly smaller than that maximum. -/
private lemma eraseMax'_eq_filter_lt {n : ℕ} (S : Finset (Fin n)) (hS : S.Nonempty) :
    S.erase (S.max' hS) = S.filter (fun j ↦ j.1 < (S.max' hS).1) := by
  ext j
  constructor
  · intro hj
    have hjS : j ∈ S := Finset.mem_of_mem_erase hj
    have hjne : j ≠ S.max' hS := Finset.ne_of_mem_erase hj
    have hjlt : j.1 < (S.max' hS).1 := by
      have hjle : j ≤ S.max' hS := Finset.le_max' S j hjS
      have hjval_ne : j.1 ≠ (S.max' hS).1 := by
        intro hEq
        apply hjne
        exact Fin.ext hEq
      exact lt_of_le_of_ne hjle hjval_ne
    simpa [Finset.mem_filter, hjS] using hjlt
  · intro hj
    have hjS : j ∈ S := (Finset.mem_filter.1 hj).1
    have hjlt : j.1 < (S.max' hS).1 := (Finset.mem_filter.1 hj).2
    have hjne : j ≠ S.max' hS := by
      intro hEq
      exact lt_irrefl _ (hEq ▸ hjlt)
    exact Finset.mem_erase.2 ⟨hjne, hjS⟩

/-- Helper for Exercise 4.25: summing over an identity-order greedy prefix is the same as summing
over `Fin r` and then casting into `Fin n`. -/
private lemma sum_submodularGreedyPrefix_eq_sum_fin {n : ℕ}
    (x : Fin n → ℝ) {r : ℕ} (hr : r ≤ n) :
    Finset.sum (submodularGreedyPrefix n r) x = ∑ j : Fin r, x (Fin.castLE hr j) := by
  classical
  let emb : Fin r ↪ Fin n := Fin.castLEEmb hr
  have hmap : (Finset.univ : Finset (Fin r)).map emb = submodularGreedyPrefix n r := by
    ext i
    constructor
    · intro hi
      rcases Finset.mem_map.1 hi with ⟨j, -, rfl⟩
      simpa [emb, mem_submodularGreedyPrefix_iff] using j.2
    · intro hi
      have hir : i.1 < r := by
        simpa [mem_submodularGreedyPrefix_iff] using hi
      refine Finset.mem_map.2 ⟨⟨i.1, hir⟩, Finset.mem_univ _, ?_⟩
      ext
      simp [emb]
  calc
    Finset.sum (submodularGreedyPrefix n r) x =
        Finset.sum ((Finset.univ : Finset (Fin r)).map emb) x := by
      rw [hmap.symm]
    _ = ∑ j : Fin r, x (Fin.castLE hr j) := by
      simpa [emb] using (Finset.sum_map (f := x) emb (Finset.univ : Finset (Fin r)))

/-- Helper for Exercise 4.25: the identity-order greedy vector belongs to the submodular
polyhedron of a normalized submodular function. -/
private lemma greedyPoint_mem_submodularPolyhedron_of_submodular {n : ℕ}
    (f : Finset (Fin n) → ℝ) (hf : Submodular f) (h_empty : f ∅ = 0) :
    (fun j ↦
      f (submodularGreedyPrefix n (j.1 + 1)) - f (submodularGreedyPrefix n j.1)) ∈
        submodularPolyhedron f := by
  rw [mem_submodularPolyhedron_iff]
  intro S
  classical
  refine Finset.strongInductionOn S ?_
  intro S IH
  by_cases hS : S = ∅
  · -- The empty subset inequality is exactly the normalization `f ∅ = 0`.
    subst hS
    simp [h_empty]
  · have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.2 hS
    let m : Fin n := S.max' hS_nonempty
    have hm_mem : m ∈ S := Finset.max'_mem S hS_nonempty
    have hgm :
        f (submodularGreedyPrefix n (m.1 + 1)) - f (submodularGreedyPrefix n m.1) ≤
          f S - f (S.erase m) := by
      -- Compare the new greedy increment with the marginal of the actual maximal element of `S`.
      calc
        f (submodularGreedyPrefix n (m.1 + 1)) - f (submodularGreedyPrefix n m.1) ≤
            f (insert m (S.filter fun j ↦ j.1 < m.1)) - f (S.filter fun j ↦ j.1 < m.1) := by
              simpa [m] using greedyCoordinate_le_restrictedMarginal f hf S m
        _ = f S - f (S.erase m) := by
              rw [← eraseMax'_eq_filter_lt S hS_nonempty, Finset.insert_erase hm_mem]
    have hIH :
        Finset.sum (S.erase m)
          (fun i ↦ f (submodularGreedyPrefix n (i.1 + 1)) - f (submodularGreedyPrefix n i.1)) ≤
            f (S.erase m) := by
      -- Removing the maximum gives a strict subset, so the induction hypothesis applies.
      exact IH (S.erase m) (Finset.erase_ssubset hm_mem)
    calc
      Finset.sum S
          (fun i ↦ f (submodularGreedyPrefix n (i.1 + 1)) - f (submodularGreedyPrefix n i.1))
          =
            (f (submodularGreedyPrefix n (m.1 + 1)) - f (submodularGreedyPrefix n m.1)) +
              Finset.sum (S.erase m)
                (fun i ↦ f (submodularGreedyPrefix n (i.1 + 1)) - f (submodularGreedyPrefix n i.1)) := by
            rw [← Finset.insert_erase hm_mem, Finset.sum_insert (Finset.notMem_erase _ _)]
            simp
      _ ≤ (f S - f (S.erase m)) + f (S.erase m) := add_le_add hgm hIH
      _ = f S := by
            ring

/-- Helper for Exercise 4.25: an antitone nonnegative objective is monotone with respect to
prefix domination in identity order. -/
private lemma orderedDotProduct_le_of_prefixDominance {n : ℕ}
    (c x y : Fin n → ℝ)
    (hSorted : Antitone c)
    (hNonneg : ∀ j : Fin n, 0 ≤ c j)
    (hPrefix :
      ∀ r : ℕ, ∀ hr : r ≤ n,
        Finset.sum (submodularGreedyPrefix n r) x ≤
          Finset.sum (submodularGreedyPrefix n r) y) :
    c ⬝ᵥ x ≤ c ⬝ᵥ y := by
  cases n with
  | zero =>
      simp [dotProduct]
  | succ n =>
      let a : ℕ → ℝ := fun i ↦ if h : i < n + 1 then c ⟨i, h⟩ else 0
      let bx : ℕ → ℝ := fun i ↦ if h : i < n + 1 then x ⟨i, h⟩ else 0
      let bY : ℕ → ℝ := fun i ↦ if h : i < n + 1 then y ⟨i, h⟩ else 0
      have hxDot :
          c ⬝ᵥ x = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := by
        -- Rewrite the dot product as a range sum so Abel summation applies directly.
        calc
          c ⬝ᵥ x = Finset.sum Finset.univ (fun i : Fin (n + 1) ↦ c i * x i) := by
            simp [dotProduct]
          _ = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < n + 1 := Finset.mem_range.1 hi
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi_lt
            simp [a, bx, hi_lt, hi_le]
      have hyDot :
          c ⬝ᵥ y = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := by
        -- The same range rewrite applies to the comparison vector `y`.
        calc
          c ⬝ᵥ y = Finset.sum Finset.univ (fun i : Fin (n + 1) ↦ c i * y i) := by
            simp [dotProduct]
          _ = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < n + 1 := Finset.mem_range.1 hi
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi_lt
            simp [a, bY, hi_lt, hi_le]
      have hxPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bx =
              Finset.sum (submodularGreedyPrefix (n + 1) r) x := by
        intro r hr
        -- Reindex the ordered range back to the corresponding greedy prefix.
        calc
          Finset.sum (Finset.range r) bx = ∑ j : Fin r, x (Fin.castLE hr j) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < r := Finset.mem_range.1 hi
            have hin : i < n + 1 := lt_of_lt_of_le hi_lt hr
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hin
            simp [bx, hi_lt, hi_le]
          _ = Finset.sum (submodularGreedyPrefix (n + 1) r) x := by
            simpa using (sum_submodularGreedyPrefix_eq_sum_fin x hr).symm
      have hyPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bY =
              Finset.sum (submodularGreedyPrefix (n + 1) r) y := by
        intro r hr
        -- The same reindexing identifies the ordered prefix sums of `y`.
        calc
          Finset.sum (Finset.range r) bY = ∑ j : Fin r, y (Fin.castLE hr j) := by
            rw [Finset.sum_fin_eq_sum_range]
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hi_lt : i < r := Finset.mem_range.1 hi
            have hin : i < n + 1 := lt_of_lt_of_le hi_lt hr
            have hi_le : i ≤ n := Nat.lt_succ_iff.mp hin
            simp [bY, hi_lt, hi_le]
          _ = Finset.sum (submodularGreedyPrefix (n + 1) r) y := by
            simpa using (sum_submodularGreedyPrefix_eq_sum_fin y hr).symm
      have hxParts :
          Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) =
            a n * Finset.sum (Finset.range (n + 1)) bx -
              Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) := by
        -- Abel summation rewrites the weighted ordered sum into total and prefix terms.
        simpa [smul_eq_mul] using Finset.sum_range_by_parts a bx (n + 1)
      have hyParts :
          Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) =
            a n * Finset.sum (Finset.range (n + 1)) bY -
              Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) := by
        -- Apply the same identity to the comparison vector `y`.
        simpa [smul_eq_mul] using Finset.sum_range_by_parts a bY (n + 1)
      have hxExpr :
          c ⬝ᵥ x =
            a n * Finset.sum (Finset.range (n + 1)) bx +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
        have hsumFlipBx :
            -Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) =
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        calc
          c ⬝ᵥ x = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bx i) := hxDot
          _ = a n * Finset.sum (Finset.range (n + 1)) bx -
                Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx) := hxParts
          _ = a n * Finset.sum (Finset.range (n + 1)) bx +
                (-Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bx)) := by
                ring
          _ = a n * Finset.sum (Finset.range (n + 1)) bx +
                Finset.sum (Finset.range n)
                  (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := by
                rw [hsumFlipBx]
      have hyExpr :
          c ⬝ᵥ y =
            a n * Finset.sum (Finset.range (n + 1)) bY +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
        have hsumFlipBY :
            -Finset.sum (Finset.range n)
                (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) =
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
          rw [← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl ?_
          intro i hi
          ring
        calc
          c ⬝ᵥ y = Finset.sum (Finset.range (n + 1)) (fun i ↦ a i * bY i) := hyDot
          _ = a n * Finset.sum (Finset.range (n + 1)) bY -
                Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY) := hyParts
          _ = a n * Finset.sum (Finset.range (n + 1)) bY +
                (-Finset.sum (Finset.range n)
                  (fun i ↦ (a (i + 1) - a i) * Finset.sum (Finset.range (i + 1)) bY)) := by
                ring
          _ = a n * Finset.sum (Finset.range (n + 1)) bY +
                Finset.sum (Finset.range n)
                  (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
                rw [hsumFlipBY]
      have hLastNonneg : 0 ≤ a n := by
        simp [a, hNonneg]
      have hGapNonneg : ∀ i ∈ Finset.range n, 0 ≤ a i - a (i + 1) := by
        intro i hi
        have hi_lt : i < n := Finset.mem_range.1 hi
        have hi0 : i < n + 1 := lt_trans hi_lt (Nat.lt_succ_self n)
        have hi1 : i + 1 < n + 1 := Nat.succ_lt_succ hi_lt
        have hstep : c ⟨i + 1, hi1⟩ ≤ c ⟨i, hi0⟩ := by
          exact hSorted (show (⟨i, hi0⟩ : Fin (n + 1)) ≤ ⟨i + 1, hi1⟩ by
            exact Nat.le_succ i)
        have hstep' : a (i + 1) ≤ a i := by
          have hi_le : i ≤ n := Nat.lt_succ_iff.mp hi0
          simpa [a, hi_lt, hi_le] using hstep
        linarith
      have hPrefixRange :
          ∀ r : ℕ, ∀ hr : r ≤ n + 1,
            Finset.sum (Finset.range r) bx ≤ Finset.sum (Finset.range r) bY := by
        intro r hr
        rw [hxPrefixRange r hr, hyPrefixRange r hr]
        exact hPrefix r hr
      have hLastLe :
          a n * Finset.sum (Finset.range (n + 1)) bx ≤
            a n * Finset.sum (Finset.range (n + 1)) bY := by
        exact mul_le_mul_of_nonneg_left (hPrefixRange (n + 1) le_rfl) hLastNonneg
      have hGapLe :
          Finset.sum (Finset.range n)
              (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) ≤
            Finset.sum (Finset.range n)
              (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) := by
        refine Finset.sum_le_sum ?_
        intro i hi
        exact mul_le_mul_of_nonneg_left
          (hPrefixRange (i + 1) (Nat.succ_le_succ (Nat.le_of_lt (Finset.mem_range.1 hi))))
          (hGapNonneg i hi)
      calc
        c ⬝ᵥ x =
            a n * Finset.sum (Finset.range (n + 1)) bx +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bx) := hxExpr
        _ ≤ a n * Finset.sum (Finset.range (n + 1)) bY +
              Finset.sum (Finset.range n)
                (fun i ↦ (a i - a (i + 1)) * Finset.sum (Finset.range (i + 1)) bY) :=
            add_le_add hLastLe hGapLe
        _ = c ⬝ᵥ y := hyExpr.symm

/-- Helper for Exercise 4.25: relabeling every member of a laminar family along an equivalence
preserves laminarity. -/
private lemma isLaminarSubsetFamily_image_relabelFinset {γ β : Type*}
    [DecidableEq γ] [DecidableEq β] (e : γ ≃ β)
    {𝒮 : Finset (Finset γ)} (h𝒮 : IsLaminarSubsetFamily 𝒮) :
    IsLaminarSubsetFamily (𝒮.image (relabelFinset e)) := by
  intro S T hS hT hST
  rcases Finset.mem_image.1 hS with ⟨S', hS', hSdef⟩
  rcases Finset.mem_image.1 hT with ⟨T', hT', hTdef⟩
  subst hSdef hTdef
  have hST' : (S' ∩ T').Nonempty := by
    rcases hST with ⟨b, hb⟩
    refine ⟨e.symm b, ?_⟩
    simpa [Finset.mem_inter] using hb
  rcases h𝒮 hS' hT' hST' with hsub | hsub
  · left
    intro b hb
    rw [mem_relabelFinset] at hb ⊢
    exact hsub hb
  · right
    intro b hb
    rw [mem_relabelFinset] at hb ⊢
    exact hsub hb

/-- Helper for Exercise 4.25: the incidence vectors of the identity-order greedy prefix chain are
linearly independent. -/
private lemma linearIndependent_greedyPrefixIndicators (n : ℕ) :
    LinearIndependent ℝ
      (fun r : Fin n ↦ fun j ↦ if j ∈ submodularGreedyPrefix n (r.1 + 1) then (1 : ℝ) else 0) := by
  classical
  let v : Fin n → Fin n → ℝ :=
    fun r j ↦ if j ∈ submodularGreedyPrefix n (r.1 + 1) then (1 : ℝ) else 0
  have hmain :
      ∀ s : Finset (Fin n), ∀ a : Fin n → ℝ,
        (∀ i ∉ s, a i = 0) →
          Finset.sum s (fun i ↦ a i • v i) = 0 →
            ∀ i : Fin n, a i = 0 := by
    intro s
    refine Finset.strongInductionOn s ?_
    intro s IH a ha hsum i
    by_cases hs : s = ∅
    · -- Outside the empty support all coefficients already vanish.
      exact ha i (hs ▸ by simp)
    · have hs_nonempty : s.Nonempty := Finset.nonempty_iff_ne_empty.2 hs
      let m : Fin n := s.max' hs_nonempty
      have hm_mem : m ∈ s := Finset.max'_mem s hs_nonempty
      have hm_zero : a m = 0 := by
        -- Evaluating the dependence relation at the maximal coordinate isolates the top coefficient.
        have hAtFun : (Finset.sum s (fun j ↦ a j • v j)) m = 0 := by
          simpa using congrArg (fun z : Fin n → ℝ ↦ z m) hsum
        have hAt : Finset.sum s (fun j ↦ a j * v j m) = 0 := by
          simpa [Pi.smul_apply, smul_eq_mul] using hAtFun
        have hRest :
            Finset.sum (s.erase m) (fun j ↦ a j * v j m) = 0 := by
          refine Finset.sum_eq_zero ?_
          intro j hj
          have hjs : j ∈ s := Finset.mem_of_mem_erase hj
          have hjm : j ≠ m := Finset.ne_of_mem_erase hj
          have hjle : j ≤ m := Finset.le_max' s j hjs
          have hjlt : j < m := lt_of_le_of_ne hjle hjm
          have hm_not_mem : m ∉ submodularGreedyPrefix n (j.1 + 1) := by
            rw [mem_submodularGreedyPrefix_iff]
            omega
          have hm_not_le : ¬ m ≤ j := not_le_of_gt hjlt
          simp [v, mem_submodularGreedyPrefix_iff, hm_not_le]
        have hsplit :
            Finset.sum s (fun j ↦ a j * v j m) =
              a m * v m m + Finset.sum (s.erase m) (fun j ↦ a j * v j m) := by
          simpa [add_comm] using
            (Finset.sum_erase_add (s := s) (a := m) (f := fun j ↦ a j * v j m) hm_mem).symm
        have hm_coeff : a m * v m m = 0 := by
          rw [hsplit, hRest] at hAt
          simpa using hAt
        simpa [v, mem_submodularGreedyPrefix_iff] using hm_coeff
      have hEraseSupport : ∀ j ∉ s.erase m, a j = 0 := by
        intro j hj
        by_cases hjm : j = m
        · simpa [hjm] using hm_zero
        · exact ha j (by
            intro hjs
            exact hj (Finset.mem_erase.2 ⟨hjm, hjs⟩))
      have hEraseSum : Finset.sum (s.erase m) (fun j ↦ a j • v j) = 0 := by
        -- After the maximal coefficient vanishes, the same dependence relation remains on the erase.
        have hsum' := hsum
        rw [← Finset.insert_erase hm_mem, Finset.sum_insert (Finset.notMem_erase _ _)] at hsum'
        simpa [hm_zero] using hsum'
      by_cases him : i = m
      · simpa [him] using hm_zero
      · exact IH (s.erase m) (Finset.erase_ssubset hm_mem) a hEraseSupport hEraseSum i
  simpa [v] using ((linearIndependent_iff'').2 hmain)

lemma exists_laminar_active_independent_family_of_active_independent_family
    {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ) (hf_submodular : Submodular f) {xbar : α → ℝ}
    (hxbar_mem : xbar ∈ submodularPolyhedron f) {T : α → Finset α}
    (hactive : ∀ i : α, (T i).sum xbar = f (T i))
    (hlinear :
      LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ T i then (1 : ℝ) else 0)) :
    ∃ S : α → Finset α,
      IsLaminarSubsetFamily (Finset.univ.image S) ∧
        (∀ i : α, (S i).sum xbar = f (S i)) ∧
          LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ S i then (1 : ℝ) else 0) := by
  classical
  -- Route correction: the broken one-set uncrossing potential is no longer the frontier. The
  -- proved API above now exposes `xbar` uniquely by the row-sum objective attached to the active
  -- independent family, so the remaining work is the ordered-greedy transport from that exposing
  -- objective to a laminar chain of tight prefix sets.
  let c : α → ℝ := activeFamilyObjective T
  have hc_support :
      (∀ x : α → ℝ, x ∈ submodularPolyhedron f → c ⬝ᵥ x ≤ c ⬝ᵥ xbar) ∧
        (∀ x : α → ℝ, x ∈ submodularPolyhedron f → c ⬝ᵥ x = c ⬝ᵥ xbar → x = xbar) :=
    activeFamilyObjective_supports_and_uniquely_exposes f hxbar_mem hactive hlinear
  have hEmptyNonneg : 0 ≤ f ∅ := by
    simpa using hxbar_mem (∅ : Finset α)
  have hc_nonneg : ∀ j : α, 0 ≤ c j := by
    intro j
    -- The row-sum objective counts how many active sets contain `j`.
    unfold c activeFamilyObjective
    exact Finset.sum_nonneg fun i hi ↦ by
      by_cases hij : j ∈ T i <;> simp [hij]
  let e : Fin (Fintype.card α) ≃ α := (Fintype.equivFin α).symm
  let L : (α → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card α) → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e
  let f0 : Finset α → ℝ := normalizeEmpty f
  have hf0_sub : Submodular f0 := submodular_normalizeEmpty f hf_submodular hEmptyNonneg
  have hxbar_f0 : xbar ∈ submodularPolyhedron f0 := by
    exact (mem_submodularPolyhedron_normalizeEmpty_iff f hEmptyNonneg).2 hxbar_mem
  let fFin : Finset (Fin (Fintype.card α)) → ℝ := fun S ↦ f0 (relabelFinset e S)
  have hfFin_sub : Submodular fFin := by
    -- The greedy construction is carried out only after this one-time transport to `Fin`.
    simpa [fFin, f0] using submodular_relabelFinset e.symm f0 hf0_sub
  have hxbarFin_mem : L xbar ∈ submodularPolyhedron fFin := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    -- Transport each subset inequality through the coordinate equivalence once.
    simpa [fFin, f0, L, LinearEquiv.funCongrLeft_apply, sum_relabelFinset] using
      hxbar_f0 (relabelFinset e S)
  let cFin : Fin (Fintype.card α) → ℝ := fun j ↦ c (e j)
  let σ : Equiv.Perm (Fin (Fintype.card α)) :=
    Tuple.sort (fun j ↦ OrderDual.toDual (cFin j))
  let cSorted : Fin (Fintype.card α) → ℝ := fun j ↦ cFin (σ j)
  have hSorted : Antitone cSorted := by
    simpa [cSorted, σ] using Tuple.monotone_sort (fun j ↦ OrderDual.toDual (cFin j))
  have hSorted_nonneg : ∀ j : Fin (Fintype.card α), 0 ≤ cSorted j := by
    intro j
    simpa [cSorted, cFin] using hc_nonneg (e (σ j))
  let fSorted : Finset (Fin (Fintype.card α)) → ℝ := fun S ↦ fFin (relabelFinset σ S)
  have hfSorted_sub : Submodular fSorted := by
    -- Sorting the objective is paired with the same permutation on the ground-set labels.
    simpa [fSorted, fFin] using submodular_relabelFinset σ.symm fFin hfFin_sub
  let xSorted : Fin (Fintype.card α) → ℝ := fun j ↦ L xbar (σ j)
  have hfSorted_empty : fSorted ∅ = 0 := by
    -- The normalize-empty step survives both relabelings unchanged at the empty set.
    simp [fSorted, fFin, f0, normalizeEmpty, relabelFinset]
  have hxSorted_mem : xSorted ∈ submodularPolyhedron fSorted := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset σ S) (L xbar) = Finset.sum S xSorted := by
      simpa [xSorted, Function.comp] using (sum_relabelFinset σ (L xbar) S)
    -- Move the already-proved `Fin`-world feasibility across the sorting permutation once.
    calc
      Finset.sum S xSorted = Finset.sum (relabelFinset σ S) (L xbar) := hsum.symm
      _ ≤ fFin (relabelFinset σ S) := hxbarFin_mem (relabelFinset σ S)
      _ = fSorted S := rfl
  let g : Fin (Fintype.card α) → ℝ := fun j ↦
    fSorted (submodularGreedyPrefix (Fintype.card α) (j.1 + 1)) -
      fSorted (submodularGreedyPrefix (Fintype.card α) j.1)
  have hg_prefix :
      ∀ r : ℕ, ∀ hr : r ≤ Fintype.card α,
        Finset.sum (submodularGreedyPrefix (Fintype.card α) r) g =
          fSorted (submodularGreedyPrefix (Fintype.card α) r) := by
    intro r hr
    -- This is the canonical prefix-tightness identity for the sorted greedy vector.
    simpa [g] using greedyPrefixSum_eq_prefixValue fSorted hfSorted_empty r hr
  let _ := hc_support
  let _ := hxbarFin_mem
  let _ := hSorted
  let _ := hSorted_nonneg
  let _ := hfSorted_sub
  let _ := hfSorted_empty
  let _ := hxSorted_mem
  let _ := xSorted
  let _ := g
  let _ := hg_prefix
  let prefixFamily : Fin (Fintype.card α) → Finset α := fun r ↦
    relabelFinset e (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)))
  let π : α ≃ Fin (Fintype.card α) := (Fintype.equivFin α).trans σ.symm
  let xGreedyFin : Fin (Fintype.card α) → ℝ := fun j ↦ g (σ.symm j)
  let xGreedyOrig : α → ℝ := L.symm xGreedyFin
  have hg_mem : g ∈ submodularPolyhedron fSorted := by
    -- The remaining greedy candidate is feasible by the standard diminishing-returns induction.
    simpa [g] using
      greedyPoint_mem_submodularPolyhedron_of_submodular fSorted hfSorted_sub hfSorted_empty
  have hgreedy_opt : cSorted ⬝ᵥ xSorted ≤ cSorted ⬝ᵥ g := by
    -- Prefix domination plus Abel summation compares the exposed point to the greedy point.
    refine orderedDotProduct_le_of_prefixDominance cSorted xSorted g hSorted hSorted_nonneg ?_
    intro r hr
    calc
      Finset.sum (submodularGreedyPrefix (Fintype.card α) r) xSorted ≤
          fSorted (submodularGreedyPrefix (Fintype.card α) r) :=
        hxSorted_mem (submodularGreedyPrefix (Fintype.card α) r)
      _ = Finset.sum (submodularGreedyPrefix (Fintype.card α) r) g := (hg_prefix r hr).symm
  have hxGreedyFin_mem : xGreedyFin ∈ submodularPolyhedron fFin := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset σ.symm S) g = Finset.sum S xGreedyFin := by
      simpa [xGreedyFin, Function.comp] using (sum_relabelFinset σ.symm g S)
    -- Undo the sorting permutation once to return to the unsorted `Fin` coordinates.
    calc
      Finset.sum S xGreedyFin = Finset.sum (relabelFinset σ.symm S) g := hsum.symm
      _ ≤ fSorted (relabelFinset σ.symm S) := hg_mem (relabelFinset σ.symm S)
      _ = fFin S := by
            simpa [fSorted] using
              congrArg fFin (relabelFinset_relabelFinset (σ.symm) S)
  have hxGreedyOrig_f0 : xGreedyOrig ∈ submodularPolyhedron f0 := by
    rw [mem_submodularPolyhedron_iff]
    intro S
    have hsum :
        Finset.sum (relabelFinset e.symm S) xGreedyFin = Finset.sum S xGreedyOrig := by
      calc
        Finset.sum (relabelFinset e.symm S) xGreedyFin =
            Finset.sum S (fun a ↦ xGreedyFin (e.symm a)) := by
              simpa using sum_relabelFinset e.symm xGreedyFin S
        _ = Finset.sum S xGreedyOrig := by
              simp [xGreedyOrig, xGreedyFin, L, LinearEquiv.funCongrLeft_apply]
    -- Undo the original `Fin`-labeling transport once to return to the ground type `α`.
    calc
      Finset.sum S xGreedyOrig = Finset.sum (relabelFinset e.symm S) xGreedyFin := hsum.symm
      _ ≤ fFin (relabelFinset e.symm S) := hxGreedyFin_mem (relabelFinset e.symm S)
      _ = f0 S := by
            simpa [fFin] using
              congrArg f0 (relabelFinset_relabelFinset e.symm S)
  have hxGreedyOrig_mem : xGreedyOrig ∈ submodularPolyhedron f := by
    exact (mem_submodularPolyhedron_normalizeEmpty_iff f hEmptyNonneg).1 hxGreedyOrig_f0
  have hxbarValue : c ⬝ᵥ xbar = cSorted ⬝ᵥ xSorted := by
    -- Reindex the exposed objective first to `Fin`, then into sorted order.
    calc
      c ⬝ᵥ xbar = ∑ a, c a * xbar a := by
        simp [dotProduct]
      _ = ∑ a, cFin (e.symm a) * L xbar (e.symm a) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [cFin, L, LinearEquiv.funCongrLeft_apply]
      _ = ∑ j : Fin (Fintype.card α), cFin j * L xbar j := by
            simpa using (Equiv.sum_comp (e := e.symm) (g := fun j : Fin (Fintype.card α) ↦
              cFin j * L xbar j))
      _ = ∑ j : Fin (Fintype.card α), cFin (σ j) * L xbar (σ j) := by
            symm
            simpa using (Equiv.sum_comp (e := σ) (g := fun j : Fin (Fintype.card α) ↦
              cFin j * L xbar j))
      _ = cSorted ⬝ᵥ xSorted := by
            simp [dotProduct, cSorted, xSorted]
  have hxGreedyValue : c ⬝ᵥ xGreedyOrig = cSorted ⬝ᵥ g := by
    -- The same two reindexings identify the transported greedy point with its sorted coordinates.
    calc
      c ⬝ᵥ xGreedyOrig = ∑ a, c a * xGreedyOrig a := by
        simp [dotProduct]
      _ = ∑ a, cFin (e.symm a) * xGreedyFin (e.symm a) := by
            refine Finset.sum_congr rfl ?_
            intro a ha
            simp [cFin, xGreedyOrig, xGreedyFin, L, LinearEquiv.funCongrLeft_apply]
      _ = ∑ j : Fin (Fintype.card α), cFin j * xGreedyFin j := by
            simpa using (Equiv.sum_comp (e := e.symm) (g := fun j : Fin (Fintype.card α) ↦
              cFin j * xGreedyFin j))
      _ = ∑ j : Fin (Fintype.card α), cFin (σ j) * xGreedyFin (σ j) := by
            symm
            simpa using (Equiv.sum_comp (e := σ) (g := fun j : Fin (Fintype.card α) ↦
              cFin j * xGreedyFin j))
      _ = cSorted ⬝ᵥ g := by
            simp [dotProduct, cSorted, xGreedyFin]
  have hxbar_le_greedy : c ⬝ᵥ xbar ≤ c ⬝ᵥ xGreedyOrig := by
    -- The sorted greedy optimality gives the reverse inequality needed for uniqueness.
    calc
      c ⬝ᵥ xbar = cSorted ⬝ᵥ xSorted := hxbarValue
      _ ≤ cSorted ⬝ᵥ g := hgreedy_opt
      _ = c ⬝ᵥ xGreedyOrig := hxGreedyValue.symm
  have hgreedy_eq_obj : c ⬝ᵥ xGreedyOrig = c ⬝ᵥ xbar := by
    exact le_antisymm (hc_support.1 _ hxGreedyOrig_mem) hxbar_le_greedy
  have hxGreedy_eq : xGreedyOrig = xbar := by
    exact hc_support.2 _ hxGreedyOrig_mem hgreedy_eq_obj
  have hprefixFamily_active :
      ∀ r : Fin (Fintype.card α), (prefixFamily r).sum xbar = f (prefixFamily r) := by
    intro r
    have hmem : e (σ r) ∈ prefixFamily r := by
      simp [prefixFamily, mem_submodularGreedyPrefix_iff]
    have hne : prefixFamily r ≠ ∅ := Finset.ne_empty_of_mem hmem
    have hsumE :
        Finset.sum (prefixFamily r) xGreedyOrig =
          Finset.sum
            (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))) xGreedyFin := by
      calc
        Finset.sum (prefixFamily r) xGreedyOrig =
            Finset.sum
              (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)))
              (fun j ↦ xGreedyOrig (e j)) := by
                simpa [prefixFamily] using
                  sum_relabelFinset e xGreedyOrig
                    (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)))
        _ = Finset.sum
              (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))) xGreedyFin := by
                refine Finset.sum_congr rfl ?_
                intro j hj
                simp [xGreedyOrig, xGreedyFin, L, LinearEquiv.funCongrLeft_apply]
    have hsumσ :
        Finset.sum
            (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))) xGreedyFin =
          Finset.sum (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)) g := by
      calc
        Finset.sum
            (relabelFinset σ (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))) xGreedyFin =
          Finset.sum (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))
            (fun j ↦ xGreedyFin (σ j)) := by
              simpa using
                sum_relabelFinset σ xGreedyFin
                  (submodularGreedyPrefix (Fintype.card α) (r.1 + 1))
        _ = Finset.sum (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)) g := by
              refine Finset.sum_congr rfl ?_
              intro j hj
              simp [xGreedyFin]
    -- The transported greedy point is tight on every transported prefix set.
    calc
      (prefixFamily r).sum xbar = (prefixFamily r).sum xGreedyOrig := by
        simp [hxGreedy_eq]
      _ = Finset.sum (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)) g := by
            rw [hsumE, hsumσ]
      _ = fSorted (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)) := by
            exact hg_prefix (r.1 + 1) (Nat.succ_le_of_lt r.2)
      _ = f0 (prefixFamily r) := rfl
      _ = f (prefixFamily r) := normalizeEmpty_of_ne_empty f hne
  have hLaminarPrefix : IsLaminarSubsetFamily (Finset.univ.image prefixFamily) := by
    -- The canonical prefix chain stays laminar under the sorting permutation and ground-set
    -- relabeling.
    simpa [prefixFamily, Finset.image_image] using
      (isLaminarSubsetFamily_image_relabelFinset e <|
        isLaminarSubsetFamily_image_relabelFinset σ <|
          isLaminarSubsetFamily_image_submodularGreedyPrefix (Fintype.card α))
  have hlinearPrefixFin :
      LinearIndependent ℝ
        (fun r : Fin (Fintype.card α) ↦
          fun j ↦ if j ∈ submodularGreedyPrefix (Fintype.card α) (r.1 + 1) then (1 : ℝ) else 0) :=
    linearIndependent_greedyPrefixIndicators (Fintype.card α)
  have hlinearPrefixSorted :
      LinearIndependent ℝ
        (fun r : Fin (Fintype.card α) ↦
          fun j ↦ if j ∈ relabelFinset σ
            (submodularGreedyPrefix (Fintype.card α) (r.1 + 1)) then (1 : ℝ) else 0) := by
    let Lσ : (Fin (Fintype.card α) → ℝ) ≃ₗ[ℝ] (Fin (Fintype.card α) → ℝ) :=
      LinearEquiv.funCongrLeft ℝ ℝ σ.symm
    have hmap := hlinearPrefixFin.map' Lσ.toLinearMap (by simp)
    -- Relabeling the coordinates by `σ` is a linear equivalence of the ambient function space.
    simpa [Lσ, LinearEquiv.funCongrLeft_apply, relabelFinset] using hmap
  have hlinearPrefix :
      LinearIndependent ℝ
        (fun r : Fin (Fintype.card α) ↦
          fun a ↦ if a ∈ prefixFamily r then (1 : ℝ) else 0) := by
    have hmap := hlinearPrefixSorted.map' L.symm.toLinearMap (by simp)
    -- Relabeling the coordinates by `e` transports the same independent chain to `α`.
    simpa [prefixFamily, L, LinearEquiv.funCongrLeft_apply, relabelFinset] using hmap
  let S : α → Finset α := fun a ↦ prefixFamily (π a)
  have himageS : Finset.univ.image S = Finset.univ.image prefixFamily := by
    apply Finset.ext
    intro U
    constructor
    · intro hU
      rcases Finset.mem_image.1 hU with ⟨a, _, rfl⟩
      exact Finset.mem_image.2 ⟨π a, Finset.mem_univ _, rfl⟩
    · intro hU
      rcases Finset.mem_image.1 hU with ⟨r, _, rfl⟩
      exact Finset.mem_image.2 ⟨π.symm r, Finset.mem_univ _, by simp [S, π]⟩
  have hactiveS : ∀ a : α, (S a).sum xbar = f (S a) := by
    intro a
    simpa [S] using hprefixFamily_active (π a)
  have hlinearS :
      LinearIndependent ℝ (fun a : α ↦ fun j ↦ if j ∈ S a then (1 : ℝ) else 0) := by
    -- Reindex the independent prefix chain by the sorted position of each ground element.
    simpa [S, π] using hlinearPrefix.comp π π.injective
  refine ⟨S, ?_, hactiveS, hlinearS⟩
  simpa [himageS] using hLaminarPrefix

/-- Exercise 4.25. If `x̄` is a vertex of the submodular polyhedron
`P = {x ∈ ℝ^α | ∑_{j ∈ S} x_j ≤ f(S) for all S ⊆ α}` of a submodular function `f` on a finite
ground type `α`, then there are `|α|` active inequalities whose coefficient vectors are linearly
independent and whose defining subsets form a laminar family. -/
theorem vertex_submodularPolyhedron_has_laminar_active_inequalities
    {α : Type} [Fintype α] [DecidableEq α]
    (f : Finset α → ℝ)
    (hf_submodular : Submodular f)
    {xbar : α → ℝ}
    (hxbar_vertex : xbar ∈ (submodularPolyhedron f).extremePoints ℝ) :
    ∃ S : α → Finset α,
      IsLaminarSubsetFamily (Finset.univ.image S) ∧
        (∀ i : α, (S i).sum xbar = f (S i)) ∧
          LinearIndependent ℝ (fun i : α ↦ fun j ↦ if j ∈ S i then (1 : ℝ) else 0) := by
  have hxbar_mem : xbar ∈ submodularPolyhedron f := extremePoints_subset hxbar_vertex
  obtain ⟨T, hactive, hlinear⟩ := exists_active_independent_family_of_vertex f hxbar_vertex
  -- Route correction: first extract an active basis from the matrix presentation, then uncross it
  -- to a laminar basis by the dedicated closing lemma.
  simpa using
    exists_laminar_active_independent_family_of_active_independent_family
      f hf_submodular hxbar_mem hactive hlinear
