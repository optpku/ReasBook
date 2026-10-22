/-
Authors: Changyu Zou, Chenyi Li, Guangxuan Pan, Pengfei Hao, Qiming Dai, Shu Miao, Siyuan Shao, Suwu Wu, Wanli Ma, Weiran Shi, Xinyi Guo, Xuran Sun, Yifan Bai, Yijie Wang, Yunfei Zhang, Yunxi Duan, Yuhao Jiang, Zebo Liu, Zhiyan Wang, Zichen Wang, xdedlhqhw
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@2ae8a0b0a2013b5f0bdd6a482d1872d2aa1a5462:ReasBook/Books/ConvexAnalysis_Rockafellar_1970/README.md (Contributors).
-/

import Mathlib
import Books.ConvexAnalysis_Rockafellar_1970.Chap01.section04_part5
import Books.ConvexAnalysis_Rockafellar_1970.Chap03.section11_part4
import Books.ConvexAnalysis_Rockafellar_1970.Chap04.section18_part4

section Chap04
section Section21

/-- A function `g : ℝ^n → EReal` is convex when its epigraph in `ℝ^n × ℝ` is convex. -/
def IsERealConvexFunction (n : ℕ) (g : (Fin n → ℝ) → EReal) : Prop :=
  Convex ℝ {p : (Fin n → ℝ) × ℝ | g p.1 ≤ (p.2 : EReal)}

/-- Text 21.0.1: A system of convex inequalities on `ℝ^n` is given by index sets
`I₁, I₂ ⊆ I` with `I = I₁ ∪ I₂`, extended-real bounds `αᵢ`, and convex functions
`fᵢ : ℝ^n → EReal`; the inequalities are of the form `fᵢ(x) ≤ αᵢ` for `i ∈ I₁` and
`fᵢ(x) < αᵢ` for `i ∈ I₂`. -/
structure ConvexInequalitySystem (n : ℕ) where
  idx : Type
  I1 : Set idx
  I2 : Set idx
  cover : I1 ∪ I2 = Set.univ
  alpha : idx → EReal
  f : idx → (Fin n → ℝ) → EReal
  convex_f : ∀ i : idx, IsERealConvexFunction n (f i)

/-- The pointwise satisfaction predicate for a system of convex inequalities. -/
def ConvexInequalitySystem.Satisfies {n : ℕ} (S : ConvexInequalitySystem n)
    (x : Fin n → ℝ) : Prop :=
  (∀ i : S.idx, i ∈ S.I1 → S.f i x ≤ S.alpha i) ∧
    (∀ i : S.idx, i ∈ S.I2 → S.f i x < S.alpha i)

/-- Text 21.0.2: The solution set of a system of convex inequalities is the
intersection of the convex level sets `{x | fᵢ(x) ≤ αᵢ}` for `i ∈ I₁` and
`{x | fᵢ(x) < αᵢ}` for `i ∈ I₂`. -/
def ConvexInequalitySystem.solutionSet {n : ℕ} (S : ConvexInequalitySystem n) :
    Set (Fin n → ℝ) :=
  (⋂ i : S.I1, {x : Fin n → ℝ | S.f i.1 x ≤ S.alpha i.1}) ∩
    ⋂ i : S.I2, {x : Fin n → ℝ | S.f i.1 x < S.alpha i.1}

/-- Helper for Text 21.0.3: if there are no strict-inequality indices, then `I₁ = I`. -/
lemma helperForText_21_0_3_I1_eq_univ_of_I2_empty {n : ℕ}
    (S : ConvexInequalitySystem n) (hI2 : S.I2 = ∅) : S.I1 = Set.univ := by
  -- The cover identity `I₁ ∪ I₂ = I` collapses to `I₁ = I` when `I₂ = ∅`.
  simpa [hI2] using S.cover

/-- Helper for Text 21.0.3: the feasible set equals an intersection of weak constraints
when `I₂ = ∅`. -/
lemma helperForText_21_0_3_satisfies_eq_iInter_of_no_strict {n : ℕ}
    (S : ConvexInequalitySystem n) (hI2 : S.I2 = ∅) :
    {x : Fin n → ℝ | S.Satisfies x} = ⋂ i : S.idx, {x : Fin n → ℝ | S.f i x ≤ S.alpha i} := by
  -- Route correction: the earlier route failed due a missing theorem stub; we derive
  -- the set identity directly from `Satisfies`, `S.cover`, and `hI2`.
  ext x
  constructor
  · intro hx
    -- Once `I₁ = univ`, every index contributes a weak inequality constraint.
    have hI1 : S.I1 = Set.univ :=
      helperForText_21_0_3_I1_eq_univ_of_I2_empty S hI2
    refine Set.mem_iInter.2 ?_
    intro i
    have hiI1 : i ∈ S.I1 := by
      simp [hI1]
    exact hx.1 i hiI1
  · intro hx
    -- The intersection gives all weak inequalities; the strict part is vacuous.
    refine And.intro ?_ ?_
    · intro i hiI1
      exact Set.mem_iInter.1 hx i
    · intro i hiI2
      simp [hI2] at hiI2

/-- Helper for Text 21.0.3: an intersection of closed weak-constraint sets is closed. -/
lemma helperForText_21_0_3_closed_iInter_constraints {n : ℕ}
    (S : ConvexInequalitySystem n)
    (hclosed : ∀ i : S.idx, IsClosed {x : Fin n → ℝ | S.f i x ≤ S.alpha i}) :
    IsClosed (⋂ i : S.idx, {x : Fin n → ℝ | S.f i x ≤ S.alpha i}) := by
  -- Use closedness of arbitrary intersections in a T₂ topological space.
  exact isClosed_iInter hclosed

-- Proof sketch: when `I₂ = ∅`, feasibility is an intersection of weak-inequality
-- constraints; closedness of each `fᵢ` gives closed weak sublevel sets, and
-- intersections of closed sets are closed.
/-- Text 21.0.3: For a system
`fᵢ(x) ≤ αᵢ` (`i ∈ I₁`) and `fᵢ(x) < αᵢ` (`i ∈ I₂`), if every `fᵢ` is closed
(its epigraph is closed) and there are no strict inequalities (`I₂ = ∅`),
then the set of solutions is closed. -/
theorem Text_21_0_3_solutionSet_closed_of_no_strict {n : ℕ}
    (S : ConvexInequalitySystem n)
    (hclosed : ∀ i : S.idx,
      IsClosed {p : (Fin n → ℝ) × ℝ | S.f i p.1 ≤ (p.2 : EReal)})
    (hI2 : S.I2 = ∅) :
    IsClosed {x : Fin n → ℝ | S.Satisfies x} := by
  -- With no strict constraints, feasibility is an intersection of weak sublevel sets.
  rw [helperForText_21_0_3_satisfies_eq_iInter_of_no_strict S hI2]
  apply helperForText_21_0_3_closed_iInter_constraints S
  intro i
  -- Convert the closedness hypothesis to the canonical epigraph over `univ`.
  have hclosed_epi :
      IsClosed (epigraph (S := (Set.univ : Set (Fin n → ℝ))) (S.f i)) := by
    have hepigraph_univ :
        epigraph (S := (Set.univ : Set (Fin n → ℝ))) (S.f i) =
          {p : (Fin n → ℝ) × ℝ | S.f i p.1 ≤ (p.2 : EReal)} := by
      ext p
      constructor
      · intro hp
        exact hp.2
      · intro hp
        exact ⟨by trivial, hp⟩
    simpa [hepigraph_univ] using hclosed i
  -- Closed epigraph gives closed real sublevel sets.
  have hclosed_real_sublevel :
      ∀ α : ℝ, IsClosed {x : Fin n → ℝ | S.f i x ≤ (α : EReal)} :=
    closed_sublevel_of_closed_epigraph (f := S.f i) hclosed_epi
  -- Therefore `S.f i` is lower semicontinuous.
  have hlsc : LowerSemicontinuous (S.f i) :=
    (lowerSemicontinuous_iff_closed_sublevel (f := S.f i)).2 hclosed_real_sublevel
  -- Lower semicontinuity yields closedness of all `EReal` sublevel sets.
  have hα :
      IsClosed ((S.f i) ⁻¹' Set.Iic (S.alpha i)) :=
    (lowerSemicontinuous_iff_isClosed_preimage (f := S.f i)).1 hlsc (S.alpha i)
  simpa [Set.preimage, Set.Iic] using hα

-- Proof sketch: prove each equation is equivalent to a pair of linear inequalities,
-- then apply this pointwise to every index in the system.
/-- Helper for Text 21.0.4: summing products against negated coefficients negates
the full linear form. -/
lemma helperForText_21_0_4_sum_mul_neg_coeff {n : ℕ}
    (x c : Fin n → ℝ) :
    (∑ j : Fin n, x j * (-c j)) = - (∑ j : Fin n, x j * c j) := by
  -- Rewrite every summand using `mul_neg`.
  calc
    (∑ j : Fin n, x j * (-c j)) = ∑ j : Fin n, -(x j * c j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [mul_neg]
    -- Pull the negation outside the finite sum.
    _ = - (∑ j : Fin n, x j * c j) := by
      simpa using
        (Finset.sum_neg_distrib (s := Finset.univ) (f := fun j : Fin n => x j * c j))

/-- Helper for Text 21.0.4: an equality of real numbers is equivalent to two
opposite weak inequalities. -/
lemma helperForText_21_0_4_eq_iff_le_and_neg_le_neg (s t : ℝ) :
    s = t ↔ s ≤ t ∧ (-s ≤ -t) := by
  constructor
  · intro hst
    -- Equality implies both the forward inequality and its negated counterpart.
    constructor
    · exact le_of_eq hst
    · simpa [hst]
  · intro hineq
    -- Combine the two inequalities via antisymmetry after un-negating the second.
    exact le_antisymm hineq.1 ((neg_le_neg_iff).1 hineq.2)

/-- Helper for Text 21.0.4: at each index, one linear equation is equivalent to
the pair of weak inequalities with coefficients `b i` and `-b i`. -/
lemma helperForText_21_0_4_equation_iff_pair_inequalities_at_index
    {n : ℕ} {ι : Type}
    (b : ι → (Fin n → ℝ)) (β : ι → ℝ) (x : Fin n → ℝ) (i : ι) :
    ((∑ j : Fin n, x j * b i j) = β i) ↔
      ((∑ j : Fin n, x j * b i j) ≤ β i ∧
        (∑ j : Fin n, x j * (-b i j)) ≤ -β i) := by
  -- Normalize the sum with negated coefficients to a negated linear form.
  have hrewrite :
      (∑ j : Fin n, x j * (-b i j)) = - (∑ j : Fin n, x j * b i j) :=
    helperForText_21_0_4_sum_mul_neg_coeff x (b i)
  constructor
  · intro heq
    -- Convert equality to the canonical pair `s ≤ t` and `-s ≤ -t`.
    have hpair :
        (∑ j : Fin n, x j * b i j) ≤ β i ∧
          (- (∑ j : Fin n, x j * b i j)) ≤ -β i := by
      exact (helperForText_21_0_4_eq_iff_le_and_neg_le_neg
        (∑ j : Fin n, x j * b i j) (β i)).1 heq
    constructor
    · exact hpair.1
    · simpa [hrewrite] using hpair.2
  · intro hpair
    -- Rewrite back to `-s ≤ -t` and use the scalar equivalence in reverse.
    have hneg : (- (∑ j : Fin n, x j * b i j)) ≤ -β i := by
      simpa [hrewrite] using hpair.2
    exact (helperForText_21_0_4_eq_iff_le_and_neg_le_neg
      (∑ j : Fin n, x j * b i j) (β i)).2 ⟨hpair.1, hneg⟩

/-- Text 21.0.4: A system of linear equations is equivalent to a system of convex
inequalities by replacing each equation `⟪x, bᵢ⟫ = βᵢ` with the pair
`⟪x, bᵢ⟫ ≤ βᵢ` and `⟪x, -bᵢ⟫ ≤ -βᵢ`. -/
theorem Text_21_0_4_linear_system_iff_pair_linear_inequalities {n : ℕ} {ι : Type}
    (b : ι → (Fin n → ℝ)) (β : ι → ℝ) (x : Fin n → ℝ) :
    (∀ i : ι, (∑ j : Fin n, x j * b i j) = β i) ↔
      (∀ i : ι, (∑ j : Fin n, x j * b i j) ≤ β i) ∧
        (∀ i : ι, (∑ j : Fin n, x j * (-b i j)) ≤ -β i) := by
  constructor
  · intro hEq
    -- Apply the indexwise equivalence to derive both inequality families.
    refine And.intro ?_ ?_
    · intro i
      exact ((helperForText_21_0_4_equation_iff_pair_inequalities_at_index b β x i).1
        (hEq i)).1
    · intro i
      exact ((helperForText_21_0_4_equation_iff_pair_inequalities_at_index b β x i).1
        (hEq i)).2
  · intro hIneq i
    -- Reassemble equalities pointwise from the two inequality families.
    exact (helperForText_21_0_4_equation_iff_pair_inequalities_at_index b β x i).2
      ⟨hIneq.1 i, hIneq.2 i⟩

-- Proof sketch: this is Rockafellar's convex alternative theorem (a convex Farkas-type
-- result), obtained by separation/duality: feasibility of strict inequalities on `C`
-- is equivalent to failure of any nontrivial nonnegative multiplier certificate, and
-- exactly one side holds.
/-- Helper for Theorem 21.1: if `C = ∅` and `0 < m`, then a nontrivial nonnegative
multiplier certificate exists trivially (the pointwise inequality is vacuous). -/
lemma helperForTheorem_21_1_empty_set_has_certificate {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (hm : 0 < m)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hCempty : C = ∅) :
    ∃ l : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ l i) ∧
        (∃ i : Fin m, l i ≠ 0) ∧
          (∀ x, x ∈ C →
            (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x) := by
  -- Choose one coordinate (possible since `m > 0`) and set that multiplier to `1`.
  obtain ⟨i0⟩ : Nonempty (Fin m) := (Fin.pos_iff_nonempty.mp hm)
  refine ⟨fun i => if i = i0 then 1 else 0, ?_, ?_, ?_⟩
  · -- The chosen multiplier vector is coordinatewise nonnegative.
    intro i
    by_cases hi : i = i0
    · simp [hi]
    · simp [hi]
  · -- The distinguished coordinate is nonzero, so the vector is nontrivial.
    refine ⟨i0, ?_⟩
    simp
  · -- On the empty set, the universal inequality holds vacuously.
    intro x hxC
    have hfalse : False := by
      simpa [hCempty] using hxC
    exact False.elim hfalse

/-- Helper for Theorem 21.1: if `C = ∅`, strict feasibility on `C` is impossible. -/
lemma helperForTheorem_21_1_not_strict_of_empty_set {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hCempty : C = ∅) :
    ¬ (∃ x, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal)) := by
  -- Any witness would contradict emptiness of `C`.
  intro hstrict
  rcases hstrict with ⟨x, hxC, _⟩
  simpa [hCempty] using hxC

/-- Helper for Theorem 21.1: a multiplier certificate on `C` excludes strict feasibility on `C`. -/
lemma helperForTheorem_21_1_certificate_implies_not_strict {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hcert :
      ∃ l : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ l i) ∧
          (∃ i : Fin m, l i ≠ 0) ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x)) :
    ¬ (∃ x, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal)) := by
  -- Route correction: avoid strict-mono multiplication lemmas on `EReal`; do a direct
  -- sign argument by isolating one positive multiplier and case-splitting on `EReal`.
  intro hstrict
  rcases hcert with ⟨l, hl_nonneg, hl_nontriv, hsum_nonneg_on_C⟩
  rcases hstrict with ⟨x, hxC, hxstrict⟩
  rcases hl_nontriv with ⟨i0, hi0ne⟩
  have hi0pos : 0 < l i0 :=
    lt_of_le_of_ne (hl_nonneg i0) (by simpa [eq_comm] using hi0ne)
  -- The distinguished summand is strictly negative.
  have hterm_i0_lt : ((l i0 : ℝ) : EReal) * f i0 x < 0 := by
    have hfi0neg : f i0 x < (0 : EReal) := hxstrict i0
    rcases (EReal.exists (p := fun z : EReal => z = f i0 x)).1 (by exact ⟨f i0 x, rfl⟩) with
      hbot | htop | hcoe
    · have hfi0bot : f i0 x = (⊥ : EReal) := by simpa [eq_comm] using hbot
      have hmulBot : ((l i0 : ℝ) : EReal) * (⊥ : EReal) = (⊥ : EReal) := by
        change (if 0 < l i0 then (⊥ : EReal) else if l i0 = 0 then 0 else ⊤) = ⊥
        simp [hi0pos]
      have hmul : ((l i0 : ℝ) : EReal) * f i0 x = (⊥ : EReal) := by
        simpa [hfi0bot] using hmulBot
      simpa [hmul]
    · exfalso
      have hfi0top : f i0 x = (⊤ : EReal) := by simpa [eq_comm] using htop
      have : ¬ ((⊤ : EReal) < (0 : EReal)) := by simp
      exact this (by simpa [hfi0top] using hfi0neg)
    · rcases hcoe with ⟨r, hr⟩
      have hrneg : r < 0 := by
        have : ((r : ℝ) : EReal) < 0 := by simpa [hr] using hfi0neg
        exact (EReal.coe_lt_coe_iff).1 this
      have hmulR : l i0 * r < 0 := mul_neg_of_pos_of_neg hi0pos hrneg
      have hmulE : (((l i0 * r : ℝ) : EReal) < 0) := by exact_mod_cast hmulR
      simpa [hr, EReal.coe_mul] using hmulE
  let term : Fin m → EReal := fun i => ((l i : ℝ) : EReal) * f i x
  -- Every summand is nonpositive because `lᵢ ≥ 0` and `fᵢ(x) < 0`.
  have hterm_nonpos : ∀ i : Fin m, term i ≤ 0 := by
    intro i
    exact mul_nonpos_of_nonneg_of_nonpos (by exact_mod_cast hl_nonneg i) (hxstrict i).le
  have hsum_erase_nonpos : Finset.sum (Finset.univ.erase i0) term ≤ 0 := by
    refine Finset.sum_nonpos ?_
    intro j hj
    exact hterm_nonpos j
  -- Hence the whole sum is bounded above by the strictly negative distinguished summand.
  have hsum_le_term : Finset.sum Finset.univ term ≤ term i0 := by
    have hsum_split : term i0 + Finset.sum (Finset.univ.erase i0) term = Finset.sum Finset.univ term := by
      simpa [term, add_comm, add_left_comm, add_assoc] using
        (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin m))) (a := i0) (f := term) (by simp))
    have haux : term i0 + Finset.sum (Finset.univ.erase i0) term ≤ term i0 + 0 :=
      add_le_add_right hsum_erase_nonpos (term i0)
    calc
      Finset.sum Finset.univ term = term i0 + Finset.sum (Finset.univ.erase i0) term := by
        simpa [hsum_split] using hsum_split.symm
      _ ≤ term i0 + 0 := haux
      _ = term i0 := by simp
  have hsum_lt_zero : Finset.sum Finset.univ term < 0 :=
    lt_of_le_of_lt hsum_le_term (by simpa [term] using hterm_i0_lt)
  -- This contradicts the certificate inequality at the strict-feasible point.
  exact (not_lt_of_ge (hsum_nonneg_on_C x hxC)) (by simpa [term] using hsum_lt_zero)

/-- Helper for Theorem 21.1: the transported relative interior in `Fin n → ℝ` is contained in `C`. -/
lemma helperForTheorem_21_1_riFin_subset_C {n : ℕ}
    (C : Set (Fin n → ℝ)) :
    euclideanRelativeInterior_fin n C ⊆ C := by
  intro x hxri
  -- Move to Euclidean-space coordinates and use `intrinsicInterior ⊆ set`.
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  have hxE : e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hxri
  have hxI : e.symm x ∈ intrinsicInterior ℝ (e.symm '' C) := by
    simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := e.symm '' C)] using hxE
  have hxImg : e.symm x ∈ e.symm '' C := intrinsicInterior_subset hxI
  rcases hxImg with ⟨y, hyC, hyEq⟩
  have hyx : y = x := e.symm.injective hyEq
  simpa [hyx] using hyC

/-- Helper for Theorem 21.1: failure of strict feasibility on `C` implies failure on `ri C`. -/
lemma helperForTheorem_21_1_not_strict_on_ri_of_not_strict_on_C {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hnotStrictC : ¬ (∃ x, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal))) :
    ¬ (∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ i : Fin m, f i x < (0 : EReal)) := by
  intro hstrictRi
  rcases hstrictRi with ⟨x, hxri, hxstrict⟩
  have hxC : x ∈ C := helperForTheorem_21_1_riFin_subset_C C hxri
  exact hnotStrictC ⟨x, hxC, hxstrict⟩

/-- Helper for Theorem 21.1: the open negative orthant in `ℝ^m` is nonempty and convex. -/
lemma helperForTheorem_21_1_negativeOrthant_nonempty_convex (m : ℕ) :
    (Set.Nonempty {u : Fin m → ℝ | ∀ i : Fin m, u i < 0}) ∧
      Convex ℝ {u : Fin m → ℝ | ∀ i : Fin m, u i < 0} := by
  refine ⟨?_, ?_⟩
  · -- Witness nonemptiness by the constant vector `(-1, …, -1)`.
    refine ⟨fun _ => (-1 : ℝ), ?_⟩
    intro i
    norm_num
  · -- Convex combinations preserve strict negativity coordinatewise.
    intro x hx y hy a b ha hb hab i
    have hxneg : x i < 0 := hx i
    have hyneg : y i < 0 := hy i
    have hcoord : (a • x + b • y) i = a * x i + b * y i := by
      simp [smul_eq_mul]
    rw [hcoord]
    have hapos_or_hbpos : 0 < a ∨ 0 < b := by
      by_cases ha0 : a = 0
      · right
        have hb1 : b = 1 := by linarith [hab, ha0]
        linarith [hb1]
      · left
        exact lt_of_le_of_ne ha (Ne.symm ha0)
    rcases hapos_or_hbpos with hapos | hbpos
    · have haxneg : a * x i < 0 := mul_neg_of_pos_of_neg hapos hxneg
      have hbynonpos : b * y i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hb (le_of_lt hyneg)
      have hsumneg : a * x i + b * y i < 0 + 0 := add_lt_add_of_lt_of_le haxneg hbynonpos
      simpa using hsumneg
    · have hbyneg : b * y i < 0 := mul_neg_of_pos_of_neg hbpos hyneg
      have haxnonpos : a * x i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ha (le_of_lt hxneg)
      have hsumneg : a * x i + b * y i < 0 + 0 := add_lt_add_of_le_of_lt haxnonpos hbyneg
      simpa using hsumneg

/-- Helper for Theorem 21.1: if `C` is convex and nonempty, then its transported
relative interior in `Fin n → ℝ` is nonempty. -/
lemma helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty {n : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (hCne : C.Nonempty) :
    (euclideanRelativeInterior_fin n C).Nonempty := by
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  -- Transport convexity/nonemptiness to Euclidean coordinates, then use
  -- `intrinsicInterior_nonempty` and pull the witness back to `Fin n → ℝ`.
  have hCimgConvex : Convex ℝ (e.symm '' C) := by
    simpa [e] using hC.linear_image ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)
  have hCimgNonempty : (e.symm '' C).Nonempty := hCne.image e.symm
  have hriIntrNonempty : (intrinsicInterior ℝ (e.symm '' C)).Nonempty :=
    (intrinsicInterior_nonempty hCimgConvex).2 hCimgNonempty
  have hriEuclNonempty : (euclideanRelativeInterior n (e.symm '' C)).Nonempty := by
    simpa [intrinsicInterior_eq_euclideanRelativeInterior (n := n) (C := e.symm '' C)] using
      hriIntrNonempty
  rcases hriEuclNonempty with ⟨y, hy⟩
  refine ⟨e y, ?_⟩
  exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := e y)).2
    (by simpa [e] using hy)

/-- Helper for Theorem 21.1: for convex `C`, the transported relative interior
`euclideanRelativeInterior_fin n C` is convex. -/
lemma helperForTheorem_21_1_riFin_convex {n : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C) :
    Convex ℝ (euclideanRelativeInterior_fin n C) := by
  intro x hx y hy a b ha hb hab
  let e := (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ))
  -- Convert to Euclidean coordinates, use convexity of relative interior there,
  -- then convert back via `mem_euclideanRelativeInterior_fin_iff`.
  have hCimgConvex : Convex ℝ (e.symm '' C) := by
    simpa [e] using hC.linear_image ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)
  have hriConv : Convex ℝ (euclideanRelativeInterior n (e.symm '' C)) :=
    convex_euclideanRelativeInterior n (e.symm '' C) hCimgConvex
  have hxE : e.symm x ∈ euclideanRelativeInterior n (e.symm '' C) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := x)).1 hx
  have hyE : e.symm y ∈ euclideanRelativeInterior n (e.symm '' C) :=
    (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := y)).1 hy
  have hzE : e.symm (a • x + b • y) ∈ euclideanRelativeInterior n (e.symm '' C) := by
    have hzE' : a • e.symm x + b • e.symm y ∈ euclideanRelativeInterior n (e.symm '' C) :=
      hriConv hxE hyE ha hb hab
    simpa [e, map_add, map_smul] using hzE'
  exact (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := a • x + b • y)).2 hzE

/-- Helper for Theorem 21.1: the upper-image set over `ri C` is nonempty and convex. -/
lemma helperForTheorem_21_1_riUpperImage_nonempty_convex {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (hCne : C.Nonempty)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (U : Set (Fin m → ℝ))
    (hUdef :
      U = {u : Fin m → ℝ | ∃ x ∈ euclideanRelativeInterior_fin n C,
        ∀ i : Fin m, (f i x).toReal ≤ u i}) :
    U.Nonempty ∧ Convex ℝ U := by
  refine ⟨?_, ?_⟩
  · -- Pick any `x₀ ∈ ri C` and use `u₀ᵢ = (fᵢ x₀).toReal`.
    rcases helperForTheorem_21_1_riFin_nonempty_of_convex_nonempty C hC hCne with ⟨x0, hx0ri⟩
    refine ⟨fun i => (f i x0).toReal, ?_⟩
    rw [hUdef]
    refine ⟨x0, hx0ri, ?_⟩
    intro i
    simp
  · -- Convexity follows by convexity of `ri C` and convexity of each `(f i).toReal`
    -- on its effective domain.
    intro u hu v hv a b ha hb hab
    rw [hUdef] at hu hv ⊢
    rcases hu with ⟨x, hxri, hxle⟩
    rcases hv with ⟨y, hyri, hyle⟩
    have hriConv : Convex ℝ (euclideanRelativeInterior_fin n C) :=
      helperForTheorem_21_1_riFin_convex C hC
    have hzri : a • x + b • y ∈ euclideanRelativeInterior_fin n C :=
      hriConv hxri hyri ha hb hab
    refine ⟨a • x + b • y, hzri, ?_⟩
    intro i
    have hconvToReal :
        ConvexOn ℝ (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
          (fun x => (f i x).toReal) :=
      convexOn_toReal_on_effectiveDomain (hf := hf i)
    have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := (hdom_ri i) hxri
    have hyDom : y ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := (hdom_ri i) hyri
    have hzToRealLe :
        (f i (a • x + b • y)).toReal ≤ a * (f i x).toReal + b * (f i y).toReal :=
      hconvToReal.2 hxDom hyDom ha hb hab
    have hrightLe :
        a * (f i x).toReal + b * (f i y).toReal ≤ a * u i + b * v i := by
      exact add_le_add (mul_le_mul_of_nonneg_left (hxle i) ha)
        (mul_le_mul_of_nonneg_left (hyle i) hb)
    calc
      (f i (a • x + b • y)).toReal ≤ a * (f i x).toReal + b * (f i y).toReal := hzToRealLe
      _ ≤ a * u i + b * v i := hrightLe
      _ = (a • u + b • v) i := by simp [smul_eq_mul]

/-- Helper for Theorem 21.1: if no point in `ri C` satisfies all strict inequalities,
then the real upper-image of `(f i).toReal` over `ri C` is disjoint from the open negative orthant. -/
lemma helperForTheorem_21_1_riUpperImage_disjoint_negativeOrthant {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (hNotStrictRi :
      ¬ (∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ i : Fin m, f i x < (0 : EReal))) :
    Disjoint
      {u : Fin m → ℝ | ∃ x ∈ euclideanRelativeInterior_fin n C, ∀ i : Fin m, (f i x).toReal ≤ u i}
      {u : Fin m → ℝ | ∀ i : Fin m, u i < 0} := by
  -- Any `u` in the intersection would force a strict-feasible `x ∈ ri C`, contradiction.
  refine Set.disjoint_left.2 ?_
  intro u huUpper huNeg
  rcases huUpper with ⟨x, hxri, hxUpper⟩
  have hxStrict : ∀ i : Fin m, f i x < (0 : EReal) := by
    intro i
    have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := (hdom_ri i) hxri
    have hneTop : f i x ≠ (⊤ : EReal) := mem_effectiveDomain_imp_ne_top hxDom
    have hproperFinite :
        ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) ∧
          Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) ∧
            ∀ x' ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i),
              f i x' ≠ ⊥ ∧ f i x' ≠ ⊤ :=
      (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
        (Set.univ : Set (Fin n → ℝ)) (f i)).1 (hf i)
    have hneBot : f i x ≠ (⊥ : EReal) := (hproperFinite.2.2 x hxDom).1
    have htoRealLt : (f i x).toReal < 0 := lt_of_le_of_lt (hxUpper i) (huNeg i)
    have htoRealLtE : (((f i x).toReal : ℝ) : EReal) < (0 : EReal) := by
      exact_mod_cast htoRealLt
    have hcoe : (((f i x).toReal : ℝ) : EReal) = f i x := EReal.coe_toReal hneTop hneBot
    simpa [hcoe] using htoRealLtE
  exact hNotStrictRi ⟨x, hxri, hxStrict⟩

/-- Helper for Theorem 21.1: coercion to `EReal` commutes with finite sums over real-valued terms. -/
lemma helperForTheorem_21_1_coe_finset_sum_real {ι : Type*}
    (s : Finset ι) (g : ι → ℝ) :
    (((Finset.sum s g) : ℝ) : EReal) = Finset.sum s (fun i => ((g i : ℝ) : EReal)) := by
  classical
  -- Induct on the finite set and use `EReal.coe_add` at each insertion step.
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha hs
    calc
      (((Finset.sum (insert a s) g) : ℝ) : EReal)
          = (((g a + Finset.sum s g) : ℝ) : EReal) := by
              simp [Finset.sum_insert, ha]
      _ = ((g a : ℝ) : EReal) + (((Finset.sum s g) : ℝ) : EReal) := by
            simp [EReal.coe_add]
      _ = ((g a : ℝ) : EReal) + Finset.sum s (fun i => ((g i : ℝ) : EReal)) := by
            rw [hs]
      _ = Finset.sum (insert a s) (fun i => ((g i : ℝ) : EReal)) := by
            simp [Finset.sum_insert, ha]

/-- Helper for Theorem 21.1: an upper bound on all points of the open negative orthant forces
nonnegativity of the separator normal coordinates. -/
lemma helperForTheorem_21_1_separatorNormal_nonneg_on_negativeOrthant {m : ℕ}
    (O : Set (Fin m → ℝ))
    (hOdef : O = {u : Fin m → ℝ | ∀ i : Fin m, u i < 0})
    (b : Fin m → ℝ) (β : ℝ)
    (hO_upper : ∀ x ∈ O, x ⬝ᵥ b ≤ β) :
    ∀ i : Fin m, 0 ≤ b i := by
  intro i
  -- Route correction: instead of a global cone argument, isolate one coordinate and
  -- use a one-parameter orthant perturbation that forces contradiction if `b i < 0`.
  by_contra hbi_nonneg
  have hbi_neg : b i < 0 := lt_of_not_ge hbi_nonneg
  have hb_i_ne : b i ≠ 0 := ne_of_lt hbi_neg
  let s : ℝ := (fun _ : Fin m => (-1 : ℝ)) ⬝ᵥ b
  let A : ℝ := |β - s + 1| + 1
  let t : ℝ := 1 - A / (b i)
  let o : Fin m → ℝ := fun j => if j = i then -t else (-1 : ℝ)
  have hA_pos : 0 < A := by
    have habs_nonneg : 0 ≤ |β - s + 1| := abs_nonneg (β - s + 1)
    linarith
  have ht_pos : 0 < t := by
    have hdiv_neg : A / (b i) < 0 := div_neg_of_pos_of_neg hA_pos hbi_neg
    linarith [show t = 1 - A / (b i) by rfl]
  have ho_mem : o ∈ O := by
    rw [hOdef]
    intro j
    by_cases hj : j = i
    · simp [o, hj, ht_pos]
    · simp [o, hj]
  have ho_le : o ⬝ᵥ b ≤ β := hO_upper o ho_mem
  have hodecomp : o = (fun _ : Fin m => (-1 : ℝ)) + Pi.single i (1 - t) := by
    funext j
    by_cases hj : j = i
    · subst hj
      have haux : (-t : ℝ) = (-1 : ℝ) + (1 - t) := by ring
      simpa [o] using haux
    · simp [o, hj]
  have ho_dot : o ⬝ᵥ b = s + (1 - t) * b i := by
    calc
      o ⬝ᵥ b = ((fun _ : Fin m => (-1 : ℝ)) + Pi.single i (1 - t)) ⬝ᵥ b := by
                  simp [hodecomp]
      _ = (fun _ : Fin m => (-1 : ℝ)) ⬝ᵥ b + (Pi.single i (1 - t)) ⬝ᵥ b := by
            simpa using add_dotProduct (fun _ : Fin m => (-1 : ℝ)) (Pi.single i (1 - t)) b
      _ = s + (1 - t) * b i := by
            simp [s, single_dotProduct]
  have hlin : (1 - t) * b i = A := by
    calc
      (1 - t) * b i = (A / (b i)) * b i := by
        have ht_eq : t = 1 - A / (b i) := by rfl
        linarith [ht_eq]
      _ = A := by
            field_simp [hb_i_ne]
  have hA_gt : β - s < A := by
    have hle_abs : β - s + 1 ≤ |β - s + 1| := le_abs_self (β - s + 1)
    have hA_ge : β - s + 2 ≤ A := by
      dsimp [A]
      linarith
    linarith
  have hA_le : A ≤ β - s := by
    have : s + A ≤ β := by
      calc
        s + A = s + (1 - t) * b i := by rw [hlin]
        _ = o ⬝ᵥ b := by symm; exact ho_dot
        _ ≤ β := ho_le
    linarith
  linarith

/-- Helper for Theorem 21.1: once the separator normal is coordinatewise nonnegative and nonzero,
the separator level on the negative orthant is also nonnegative. -/
lemma helperForTheorem_21_1_separatorBeta_nonneg_on_negativeOrthant {m : ℕ}
    (O : Set (Fin m → ℝ))
    (hOdef : O = {u : Fin m → ℝ | ∀ i : Fin m, u i < 0})
    (b : Fin m → ℝ) (β : ℝ)
    (hO_upper : ∀ x ∈ O, x ⬝ᵥ b ≤ β)
    (hb_ne_zero : b ≠ 0)
    (hb_nonneg : ∀ i : Fin m, 0 ≤ b i) :
    0 ≤ β := by
  -- Contradict `β < 0` by testing a small negative constant vector in the orthant.
  by_contra hβ_nonneg
  have hβ_neg : β < 0 := lt_of_not_ge hβ_nonneg
  have hb_nontriv : ∃ i : Fin m, b i ≠ 0 := by
    by_contra hnone
    apply hb_ne_zero
    funext i
    by_contra hi
    exact hnone ⟨i, hi⟩
  rcases hb_nontriv with ⟨i0, hi0_ne⟩
  have hi0_pos : 0 < b i0 := lt_of_le_of_ne (hb_nonneg i0) (by simpa [eq_comm] using hi0_ne)
  have hsum_pos : 0 < Finset.sum Finset.univ b := by
    refine Finset.sum_pos' ?_ ?_
    · intro j hj
      exact hb_nonneg j
    · exact ⟨i0, by simp, hi0_pos⟩
  let t : ℝ := (-β) / (2 * (Finset.sum Finset.univ b))
  have hden_pos : 0 < 2 * (Finset.sum Finset.univ b) := by linarith
  have ht_pos : 0 < t := by
    have hnum_pos : 0 < -β := by linarith
    have : 0 < (-β) / (2 * (Finset.sum Finset.univ b)) := div_pos hnum_pos hden_pos
    simpa [t] using this
  let o : Fin m → ℝ := (-t) • (1 : Fin m → ℝ)
  have ho_mem : o ∈ O := by
    rw [hOdef]
    intro j
    have : o j = -t := by simp [o]
    rw [this]
    linarith
  have ho_le : o ⬝ᵥ b ≤ β := hO_upper o ho_mem
  have ho_dot : o ⬝ᵥ b = (-t) * (Finset.sum Finset.univ b) := by
    calc
      o ⬝ᵥ b = ((-t) • (1 : Fin m → ℝ)) ⬝ᵥ b := by simp [o]
      _ = (-t) • ((1 : Fin m → ℝ) ⬝ᵥ b) := by
            simpa using smul_dotProduct (-t) (1 : Fin m → ℝ) b
      _ = (-t) * ((1 : Fin m → ℝ) ⬝ᵥ b) := by simp
      _ = (-t) * (Finset.sum Finset.univ b) := by simp [one_dotProduct]
  have hhalf : (-t) * (Finset.sum Finset.univ b) = β / 2 := by
    have hsum_ne_zero : (Finset.sum Finset.univ b) ≠ 0 := by linarith
    calc
      (-t) * (Finset.sum Finset.univ b)
          = (-((-β) / (2 * (Finset.sum Finset.univ b)))) * (Finset.sum Finset.univ b) := by
                simp [t]
      _ = β / 2 := by
            field_simp [hsum_ne_zero]
  have : β / 2 ≤ β := by
    calc
      β / 2 = (-t) * (Finset.sum Finset.univ b) := by symm; exact hhalf
      _ = o ⬝ᵥ b := by symm; exact ho_dot
      _ ≤ β := ho_le
  linarith

/-- Helper for Theorem 21.1: oriented separator data yields a nonnegative nontrivial real
multiplier certificate on `ri C`. -/
lemma helperForTheorem_21_1_separator_to_multiplier_on_riUpperImage {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (U O : Set (Fin m → ℝ))
    (hUdef :
      U = {u : Fin m → ℝ | ∃ x ∈ euclideanRelativeInterior_fin n C,
        ∀ i : Fin m, (f i x).toReal ≤ u i})
    (hOdef : O = {u : Fin m → ℝ | ∀ i : Fin m, u i < 0})
    (b : Fin m → ℝ) (β : ℝ)
    (hb_ne_zero : b ≠ 0)
    (hU_lower : ∀ x ∈ U, β ≤ x ⬝ᵥ b)
    (hO_upper : ∀ x ∈ O, x ⬝ᵥ b ≤ β) :
    ∃ l : Fin m → ℝ,
      (∀ i : Fin m, 0 ≤ l i) ∧
        (∃ i : Fin m, l i ≠ 0) ∧
          (∀ x ∈ euclideanRelativeInterior_fin n C,
            0 ≤ ∑ i : Fin m, l i * (f i x).toReal) := by
  have hb_nonneg : ∀ i : Fin m, 0 ≤ b i :=
    helperForTheorem_21_1_separatorNormal_nonneg_on_negativeOrthant O hOdef b β hO_upper
  have hβ_nonneg : 0 ≤ β :=
    helperForTheorem_21_1_separatorBeta_nonneg_on_negativeOrthant O hOdef b β hO_upper hb_ne_zero
      hb_nonneg
  refine ⟨b, hb_nonneg, ?_, ?_⟩
  · have hnotall : ¬ (∀ i : Fin m, b i = 0) := by
      intro hall
      apply hb_ne_zero
      funext i
      exact hall i
    exact not_forall.mp hnotall
  · intro x hxri
    -- Evaluate the separator inequality on `uₓ i = (f i x).toReal`.
    let u : Fin m → ℝ := fun i => (f i x).toReal
    have hu_mem : u ∈ U := by
      rw [hUdef]
      refine ⟨x, hxri, ?_⟩
      intro i
      exact le_rfl
    have hβ_le : β ≤ u ⬝ᵥ b := hU_lower u hu_mem
    have hdot_nonneg : 0 ≤ u ⬝ᵥ b := le_trans hβ_nonneg hβ_le
    have hdot_eq : u ⬝ᵥ b = ∑ i : Fin m, b i * (f i x).toReal := by
      unfold dotProduct
      refine Finset.sum_congr rfl ?_
      intro i hi
      ring
    simpa [hdot_eq] using hdot_nonneg

/-- Helper for Theorem 21.1: convert the `ri C` certificate from real sums of `toReal` values
to the corresponding `EReal` weighted-sum inequality. -/
lemma helperForTheorem_21_1_ri_real_certificate_to_ri_ereal_for_weightedSum {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (l : Fin m → ℝ)
    (hriReal :
      ∀ x ∈ euclideanRelativeInterior_fin n C,
        0 ≤ ∑ i : Fin m, l i * (f i x).toReal) :
    ∀ x ∈ euclideanRelativeInterior_fin n C,
      (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
  intro x hxri
  have hrealE :
      (((0 : ℝ) : EReal) ≤ (((∑ i : Fin m, l i * (f i x).toReal) : ℝ) : EReal)) := by
    exact_mod_cast hriReal x hxri
  have hsum_eq :
      (((∑ i : Fin m, l i * (f i x).toReal) : ℝ) : EReal) =
        ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
    calc
      (((∑ i : Fin m, l i * (f i x).toReal) : ℝ) : EReal)
          = ∑ i : Fin m, (((l i * (f i x).toReal : ℝ) : EReal)) := by
              exact helperForTheorem_21_1_coe_finset_sum_real (s := (Finset.univ : Finset (Fin m)))
                (g := fun i : Fin m => l i * (f i x).toReal)
      _ = ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            have hxDom : x ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) := (hdom_ri i) hxri
            have hneTop : f i x ≠ (⊤ : EReal) := mem_effectiveDomain_imp_ne_top hxDom
            have hproperFinite :
                ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) ∧
                  Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) ∧
                    ∀ x' ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i),
                      f i x' ≠ ⊥ ∧ f i x' ≠ ⊤ :=
              (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
                (Set.univ : Set (Fin n → ℝ)) (f i)).1 (hf i)
            have hneBot : f i x ≠ (⊥ : EReal) := (hproperFinite.2.2 x hxDom).1
            have hterm :
                (((l i * (f i x).toReal : ℝ) : EReal)) =
                  ((l i : EReal) * (((f i x).toReal : ℝ) : EReal)) := by
              simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc]
            calc
              (((l i * (f i x).toReal : ℝ) : EReal))
                  = ((l i : EReal) * (((f i x).toReal : ℝ) : EReal)) := hterm
              _ = ((l i : EReal) * f i x) := by
                    rw [EReal.coe_toReal hneTop hneBot]
  simpa [hsum_eq] using hrealE

/-- Helper for Theorem 21.1: promote the `ri C` weighted-sum certificate to all of `C`
via convexity and closure extension (Corollary 7.3.3). -/
lemma helperForTheorem_21_1_promote_ri_ereal_certificate_to_C {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (hCne : C.Nonempty)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i))
    (l : Fin m → ℝ)
    (hl_nonneg : ∀ i : Fin m, 0 ≤ l i)
    (hriE :
      ∀ x ∈ euclideanRelativeInterior_fin n C,
        (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x) :
    ∀ x ∈ C,
      (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
  let g : (Fin n → ℝ) → EReal := fun x => ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x
  -- Build convexity of the weighted sum from proper convexity of each summand.
  have hgOn : ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) g := by
    simpa [g] using convexFunctionOn_linearCombination_of_proper (n := n) (m := m) (lam := l)
      hl_nonneg hf
  have hg : ConvexFunction g := by
    simpa [ConvexFunction] using hgOn
  let D : Set (EuclideanSpace ℝ (Fin n)) :=
    (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm '' C
  have hDconv : Convex ℝ D := by
    simpa [D] using hC.linear_image ((EuclideanSpace.equiv (Fin n) ℝ).symm.toLinearMap)
  have hDne : D.Nonempty := by
    rcases hCne with ⟨x, hxC⟩
    exact ⟨(EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x, ⟨x, hxC, rfl⟩⟩
  have hriConv : Convex ℝ (euclideanRelativeInterior n D) :=
    convex_euclideanRelativeInterior n D hDconv
  have hriFinite :
      ∀ y ∈ euclideanRelativeInterior n D,
        g (y : Fin n → ℝ) ≠ (⊤ : EReal) ∧ g (y : Fin n → ℝ) ≠ (⊥ : EReal) := by
    intro y hyri
    have hxriFin : (y : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n C :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := (y : Fin n → ℝ))).2
        (by simpa [D] using hyri)
    have hEqCoe :
        g (y : Fin n → ℝ) = (((∑ i : Fin m, l i * (f i (y : Fin n → ℝ)).toReal) : ℝ) : EReal) := by
      calc
        g (y : Fin n → ℝ)
            = ∑ i : Fin m, ((l i : ℝ) : EReal) * f i (y : Fin n → ℝ) := by
                rfl
        _ = ∑ i : Fin m, (((l i * (f i (y : Fin n → ℝ)).toReal : ℝ) : EReal)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hyDom : (y : Fin n → ℝ) ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i) :=
                (hdom_ri i) hxriFin
              have hneTop : f i (y : Fin n → ℝ) ≠ (⊤ : EReal) :=
                mem_effectiveDomain_imp_ne_top hyDom
              have hproperFinite :
                  ConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i) ∧
                    Set.Nonempty (effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) ∧
                      ∀ x' ∈ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i),
                        f i x' ≠ ⊥ ∧ f i x' ≠ ⊤ :=
                (properConvexFunctionOn_iff_effectiveDomain_nonempty_finite
                  (Set.univ : Set (Fin n → ℝ)) (f i)).1 (hf i)
              have hneBot : f i (y : Fin n → ℝ) ≠ (⊥ : EReal) :=
                (hproperFinite.2.2 (y : Fin n → ℝ) hyDom).1
              have hterm :
                  (((l i * (f i (y : Fin n → ℝ)).toReal : ℝ) : EReal)) =
                    ((l i : EReal) * (((f i (y : Fin n → ℝ)).toReal : ℝ) : EReal)) := by
                simpa [EReal.coe_mul, mul_comm, mul_left_comm, mul_assoc]
              calc
                ((l i : EReal) * f i (y : Fin n → ℝ))
                    = ((l i : EReal) * (((f i (y : Fin n → ℝ)).toReal : ℝ) : EReal)) := by
                        rw [EReal.coe_toReal hneTop hneBot]
                _ = (((l i * (f i (y : Fin n → ℝ)).toReal : ℝ) : EReal)) := by
                      symm
                      exact hterm
        _ = (((∑ i : Fin m, l i * (f i (y : Fin n → ℝ)).toReal) : ℝ) : EReal) := by
              symm
              exact helperForTheorem_21_1_coe_finset_sum_real (s := (Finset.univ : Finset (Fin m)))
                (g := fun i : Fin m => l i * (f i (y : Fin n → ℝ)).toReal)
    constructor <;> simp [hEqCoe]
  have hriLower :
      ∀ y ∈ euclideanRelativeInterior n D,
        g (y : Fin n → ℝ) ≥ ((0 : ℝ) : EReal) := by
    intro y hyri
    have hxriFin : (y : Fin n → ℝ) ∈ euclideanRelativeInterior_fin n C :=
      (mem_euclideanRelativeInterior_fin_iff (n := n) (C := C) (x := (y : Fin n → ℝ))).2
        (by simpa [D] using hyri)
    simpa [g] using hriE (y : Fin n → ℝ) hxriFin
  have hclLower :
      ∀ y ∈ closure (euclideanRelativeInterior n D),
        g (y : Fin n → ℝ) ≥ ((0 : ℝ) : EReal) :=
    convexFunction_ge_on_closure_of_convexSet (n := n) (f := g) hg
      (C := euclideanRelativeInterior n D) hriConv hriFinite (α := 0) hriLower
  have hD_to_hriClosure : closure D ⊆ closure (euclideanRelativeInterior n D) :=
    euclidean_closure_subset_closure_relativeInterior_of_nonempty (n := n) (C := D) hDconv hDne
  intro x hxC
  -- Transport `x ∈ C` to the Euclidean model and then back to the original coordinates.
  have hxD : (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈ D := ⟨x, hxC, rfl⟩
  have hxClosureD : (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈ closure D :=
    subset_closure hxD
  have hxClosureRi :
      (EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x ∈ closure (euclideanRelativeInterior n D) :=
    hD_to_hriClosure hxClosureD
  have hxLower :
      g (((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x : EuclideanSpace ℝ (Fin n)) : Fin n → ℝ) ≥
        ((0 : ℝ) : EReal) :=
    hclLower ((EuclideanSpace.equiv (ι := Fin n) (𝕜 := ℝ)).symm x) hxClosureRi
  simpa [g] using hxLower

/-- Theorem 21.1: Let `C` be convex and let `f₁, …, fₘ` be proper convex functions with
`dom fᵢ ⊇ ri C`. Exactly one alternative holds:
(a) there exists `x ∈ C` with `fᵢ x < 0` for all `i`;
(b) there exist nonnegative multipliers `λᵢ`, not all zero, such that
`∑ i, λᵢ fᵢ x ≥ 0` for every `x ∈ C`. -/
theorem theorem21_convex_inequality_alternative {n m : ℕ}
    (C : Set (Fin n → ℝ))
    (hC : Convex ℝ C)
    (hm : 0 < m)
    (f : Fin m → (Fin n → ℝ) → EReal)
    (hf : ∀ i, ProperConvexFunctionOn (Set.univ : Set (Fin n → ℝ)) (f i))
    (hdom_ri :
      ∀ i, euclideanRelativeInterior_fin n C ⊆ effectiveDomain (Set.univ : Set (Fin n → ℝ)) (f i)) :
    Xor'
      (∃ x, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal))
      (∃ l : Fin m → ℝ,
        (∀ i : Fin m, 0 ≤ l i) ∧
          (∃ i : Fin m, l i ≠ 0) ∧
            (∀ x, x ∈ C →
              (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x)) := by
  -- Rewrite `Xor'` into the disjunctive normal form used for the two-case proof.
  rw [xor_def]
  by_cases hCempty : C = ∅
  · -- Empty-set branch: strict feasibility is impossible, while a certificate is vacuous.
    right
    refine ⟨?_, ?_⟩
    · exact helperForTheorem_21_1_empty_set_has_certificate C hm f hCempty
    · exact helperForTheorem_21_1_not_strict_of_empty_set C f hCempty
  · -- Nonempty branch: this is the core convex-separation argument from Theorem 11.3
    -- combined with the closure extension step (Corollary 7.3.3).
    -- Route correction: the old route kept this branch monolithic; we now split first by
    -- strict feasibility and discharge the strict-feasible contradiction explicitly.
    by_cases hStrictC : (∃ x, x ∈ C ∧ ∀ i : Fin m, f i x < (0 : EReal))
    · left
      refine ⟨hStrictC, ?_⟩
      -- Any global nonnegative multiplier certificate would contradict this strict point.
      intro hcert
      exact (helperForTheorem_21_1_certificate_implies_not_strict C f hcert) hStrictC
    · right
      have hNotStrictRi :
          ¬ (∃ x, x ∈ euclideanRelativeInterior_fin n C ∧ ∀ i : Fin m, f i x < (0 : EReal)) :=
        helperForTheorem_21_1_not_strict_on_ri_of_not_strict_on_C C f hStrictC
      -- Route correction: the prior route tried to jump directly to global multipliers.
      -- We now isolate the geometric setup (`U`, `O`, disjointness) before separator extraction.
      let U : Set (Fin m → ℝ) :=
        {u : Fin m → ℝ | ∃ x ∈ euclideanRelativeInterior_fin n C, ∀ i : Fin m, (f i x).toReal ≤ u i}
      let O : Set (Fin m → ℝ) := {u : Fin m → ℝ | ∀ i : Fin m, u i < 0}
      have hO_nonempty_convex : Set.Nonempty O ∧ Convex ℝ O := by
        simpa [O] using helperForTheorem_21_1_negativeOrthant_nonempty_convex m
      have hUO_disjoint : Disjoint U O := by
        simpa [U, O] using
          helperForTheorem_21_1_riUpperImage_disjoint_negativeOrthant C f hf hdom_ri hNotStrictRi
      have hUO_disjoint_intrinsic :
          Disjoint (intrinsicInterior ℝ U) (intrinsicInterior ℝ O) := by
        exact hUO_disjoint.mono intrinsicInterior_subset intrinsicInterior_subset
      have hCne : C.Nonempty := by
        by_contra hCnotne
        exact hCempty (Set.not_nonempty_iff_eq_empty.mp hCnotne)
      have hU_nonempty_convex : U.Nonempty ∧ Convex ℝ U := by
        -- Route correction: prove the geometric hypotheses for `U` first, then separate.
        exact helperForTheorem_21_1_riUpperImage_nonempty_convex C hC hCne f hf hdom_ri U rfl
      have hsepExists : ∃ H, HyperplaneSeparatesProperly m H U O := by
        exact (exists_hyperplaneSeparatesProperly_iff_disjoint_intrinsicInterior
          (n := m) (C₁ := U) (C₂ := O)
          hU_nonempty_convex.1 hO_nonempty_convex.1
          hU_nonempty_convex.2 hO_nonempty_convex.2).2 hUO_disjoint_intrinsic
      rcases hsepExists with ⟨H, hHsep⟩
      have hsepOriented :
          ∃ b β, b ≠ 0 ∧
            H = {x | x ⬝ᵥ b = β} ∧
            (∀ x ∈ U, β ≤ x ⬝ᵥ b) ∧
            (∀ x ∈ O, x ⬝ᵥ b ≤ β) ∧
            ¬ (U ⊆ H ∧ O ⊆ H) := by
        exact hyperplaneSeparatesProperly_oriented m H U O hHsep
      rcases hsepOriented with ⟨b, β, hb_ne_zero, hHdef, hU_lower, hO_upper, hNotBothInH⟩
      have _hHdef : H = {x | x ⬝ᵥ b = β} := hHdef
      have _hNotBothInH : ¬ (U ⊆ H ∧ O ⊆ H) := hNotBothInH
      -- Extract the real-valued certificate on `ri C` from the oriented separator.
      have hriRealCert :
          ∃ l : Fin m → ℝ,
            (∀ i : Fin m, 0 ≤ l i) ∧
              (∃ i : Fin m, l i ≠ 0) ∧
                (∀ x ∈ euclideanRelativeInterior_fin n C,
                  0 ≤ ∑ i : Fin m, l i * (f i x).toReal) := by
        exact helperForTheorem_21_1_separator_to_multiplier_on_riUpperImage C f U O rfl rfl b β
          hb_ne_zero hU_lower hO_upper
      rcases hriRealCert with ⟨l, hl_nonneg, hl_nontriv, hriReal⟩
      -- Convert the certificate to `EReal` on `ri C`, then promote it to all of `C`.
      have hriE :
          ∀ x ∈ euclideanRelativeInterior_fin n C,
            (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x :=
        helperForTheorem_21_1_ri_real_certificate_to_ri_ereal_for_weightedSum C f hf hdom_ri l
          hriReal
      have hglobal :
          ∀ x, x ∈ C → (0 : EReal) ≤ ∑ i : Fin m, ((l i : ℝ) : EReal) * f i x := by
        intro x hxC
        exact helperForTheorem_21_1_promote_ri_ereal_certificate_to_C C hC hCne f hf hdom_ri l
          hl_nonneg hriE x hxC
      exact ⟨⟨l, hl_nonneg, hl_nontriv, hglobal⟩, hStrictC⟩


end Section21
end Chap04
