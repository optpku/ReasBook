module

public import stacks_project.Chap05.Definition_5_11_4
public import stacks_project.Chap05.Definition_5_20_1
public import stacks_project.Chap05.Lemma_5_8_16
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import stacks_project.Chap05.Lemma_5_11_6

@[expose] public section

-- Declarations for this item will be appended below by the statement pipeline.

universe u

open TopologicalSpace

variable {X : Type u} [TopologicalSpace X]

/- Domain-style sampling for Lemma 5.20.2:
- project owner for dimension functions: `IsDimensionFunction` in `Definition_5_20_1`
- derived graded-order owner: `IsDimensionFunction.gradeOrder` on `Specialization X`
- project owner for catenarity and relative codimension: `CatenarySpace` and `codimBetween` in
  `Definition_5_11_4`
- project soberification bridge: `toIrreducibleCloseds` in `Lemma_5_8_16`
- mathlib specialization owner: `Specializes.closure_subset`

Layer triage:
- `source-facing`: Lemma 5.20.2, pairing catenarity with the codimension formula for closures of
  specialized points
- `core/canonical`: `IsDimensionFunction`, its induced `gradeOrder`, `CatenarySpace`, and
  sobriety encoded by
  `[QuasiSober X]` together with the derived instance `hδ.t0Space`
- `bridge/view`: the order comparison on `IrreducibleCloseds X` induced by a specialization

Primitive data already belongs to the upstream owners, so this file keeps the combined textbook
statement primary and derives the individual consequences from it.
-/

namespace IsDimensionFunction

section

variable [QuasiSober X] {δ : X → ℤ}

/-- Helper for Lemma 5.20.2: on a sober `T₀` space, irreducible closed subsets identify with
points in the specialization order. -/
private noncomputable def irreducible_closeds_equiv_specialization_points [T0Space X] :
    IrreducibleCloseds X ≃o Specialization X := by
  letI : PartialOrder X := specializationOrder X
  let eX : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints (α := X)
  let eS : X ≃o Specialization X :=
    { toEquiv := Specialization.toEquiv
      map_rel_iff' := by
        intro x y
        rfl }
  exact eX.trans eS

/-- Helper for Lemma 5.20.2: the sober-space generic-point equivalence restricts to the
corresponding interval of specialization-ordered points. -/
private noncomputable def irreducible_closeds_interval_equiv_generic_points [T0Space X]
    {T T' : IrreducibleCloseds X} :
    Set.Icc T T' ≃o
      Set.Icc ((irreducible_closeds_equiv_specialization_points (X := X)) T)
        ((irreducible_closeds_equiv_specialization_points (X := X)) T') where
  toFun x := ⟨(irreducible_closeds_equiv_specialization_points (X := X)) x.1,
    (irreducible_closeds_equiv_specialization_points (X := X)).monotone x.2.1,
    (irreducible_closeds_equiv_specialization_points (X := X)).monotone x.2.2⟩
  invFun y := ⟨(irreducible_closeds_equiv_specialization_points (X := X)).symm y.1,
    by
      simpa using
        (irreducible_closeds_equiv_specialization_points (X := X)).symm.monotone y.2.1,
    by
      simpa using
        (irreducible_closeds_equiv_specialization_points (X := X)).symm.monotone y.2.2⟩
  left_inv x := by
    ext
    simp [irreducible_closeds_equiv_specialization_points]
  right_inv y := by
    ext
    simp [irreducible_closeds_equiv_specialization_points]
  map_rel_iff' := by
    intro x y
    simpa using (irreducible_closeds_equiv_specialization_points (X := X)).le_iff_le

/-- Helper for Lemma 5.20.2: a dimension function is strictly monotone on the specialization
order. -/
private theorem strictMono_specialization_of_dimensionFunction [T0Space X]
    (hδ : IsDimensionFunction δ) :
    StrictMono fun x : Specialization X ↦ δ (Specialization.ofEquiv x) := by
  -- A strict increase in specialization order means the upper point specializes to the lower one,
  -- so the dimension function strictly increases when viewed on the ordered type
  -- `Specialization X`.
  intro x y hxy
  have hspecializes : Specialization.ofEquiv y ⤳ Specialization.ofEquiv x := by
    simpa using hxy.le
  simpa using hδ.strict_of_specializes hspecializes hxy.ne.symm

/-- Helper for Lemma 5.20.2: finite chains of length `n + 1` have Krull dimension `n`. -/
private theorem krullDim_fin_succ (n : ℕ) :
    Order.krullDim (Fin (n + 1)) = n := by
  -- Compare `Fin (n + 1)` with the initial interval `{0, ..., n}` in `ℕ`.
  let e : Fin (n + 1) ≃o Set.Iic n := by
    refine
      { toFun := fun i ↦ ⟨i.1, by simpa using i.is_le⟩
        invFun := fun i ↦ ⟨i.1, Nat.lt_succ_of_le i.2⟩
        left_inv := ?_
        right_inv := ?_
        map_rel_iff' := ?_ }
    · intro i
      rfl
    · intro i
      ext
      rfl
    · intro i j
      rfl
  rw [Order.krullDim_eq_of_orderIso e]
  simpa using (Order.height_eq_krullDim_Iic n).symm

/-- Helper for Lemma 5.20.2: the finite integer interval `[m, n]` has Krull dimension `n - m`. -/
private theorem krullDim_int_interval {m n : ℤ} (hmn : m ≤ n) :
    Order.krullDim (Set.Icc m n) = Int.toNat (n - m) := by
  -- Count the interval, then identify it with the corresponding finite chain.
  have hcard : Fintype.card (Set.Icc m n) = Int.toNat (n - m) + 1 := by
    have hcard' : (Fintype.card (Set.Icc m n) : ℤ) = n + 1 - m := by
      exact Int.card_fintype_Icc_of_le (a := m) (b := n) (by omega)
    have hcard'' : ((Int.toNat (n - m) + 1 : ℕ) : ℤ) = n + 1 - m := by
      norm_num [Int.toNat_of_nonneg (sub_nonneg.mpr hmn)]
      omega
    exact Int.ofNat.inj (hcard'.trans hcard''.symm)
  let e : Fin (Int.toNat (n - m) + 1) ≃o Set.Icc m n :=
    Fintype.orderIsoFinOfCardEq (Set.Icc m n) hcard
  calc
    Order.krullDim (Set.Icc m n)
        = Order.krullDim (Fin (Int.toNat (n - m) + 1)) := by
          simpa using (Order.krullDim_eq_of_orderIso e).symm
    _ = Int.toNat (n - m) := krullDim_fin_succ (Int.toNat (n - m))

/-- Helper for Lemma 5.20.2: in a bounded `ℤ`-graded order, the Krull dimension is the grade
difference between top and bottom. -/
private theorem krullDim_eq_toNat_sub_of_grade_order {α : Type*} [PartialOrder α]
    [BoundedOrder α] [GradeOrder ℤ α] :
    Order.krullDim α = Int.toNat (grade ℤ (⊤ : α) - grade ℤ (⊥ : α)) := by
  classical
  let N : ℕ := Int.toNat (grade ℤ (⊤ : α) - grade ℤ (⊥ : α))
  have hbot_top :
      grade ℤ (⊥ : α) ≤ grade ℤ (⊤ : α) := by
    exact grade_mono (bot_le : (⊥ : α) ≤ ⊤)
  apply le_antisymm
  · -- Map the graded order into the corresponding integer interval to get the upper bound.
    let g : α → Set.Icc (grade ℤ (⊥ : α)) (grade ℤ (⊤ : α)) :=
      fun x ↦ ⟨grade ℤ x, grade_mono (bot_le : (⊥ : α) ≤ x),
        grade_mono (le_top : x ≤ (⊤ : α))⟩
    have hg : StrictMono g := by
      intro x y hxy
      show grade ℤ x < grade ℤ y
      exact grade_strictMono hxy
    exact (Order.krullDim_le_of_strictMono g hg).trans (by
      simpa [N] using (krullDim_int_interval hbot_top).le)
  · -- A flag from bottom to top already has exactly one point in each integer grade.
    let s : Flag α := Classical.choice (show Nonempty (Flag α) from inferInstance)
    let gradeNat : s → ℕ :=
      fun x ↦ Int.toNat (grade ℤ x - grade ℤ (⊥ : s))
    have hgrade_strict : StrictMono gradeNat := by
      intro x y hxy
      have hxy_grade : grade ℤ x < grade ℤ y := grade_strictMono hxy
      have hbot_x : grade ℤ (⊥ : s) ≤ grade ℤ x := by
        exact grade_mono (bot_le : (⊥ : s) ≤ x)
      have hbot_y : grade ℤ (⊥ : s) ≤ grade ℤ y := by
        exact grade_mono (bot_le : (⊥ : s) ≤ y)
      dsimp [gradeNat]
      omega
    have hgrade_le : ∀ x : s, gradeNat x ≤ N := by
      intro x
      have hxtop : grade ℤ x ≤ grade ℤ (⊤ : s) := by
        exact grade_mono (le_top : x ≤ (⊤ : s))
      have hbot_x : grade ℤ (⊥ : s) ≤ grade ℤ x := by
        exact grade_mono (bot_le : (⊥ : s) ≤ x)
      dsimp [gradeNat, N]
      have htop_coe : grade ℤ (⊤ : s) = grade ℤ (⊤ : α) := by
        change grade ℤ ((⊤ : s) : α) = grade ℤ (⊤ : α)
        rfl
      have hbot_coe : grade ℤ (⊥ : s) = grade ℤ (⊥ : α) := by
        change grade ℤ ((⊥ : s) : α) = grade ℤ (⊥ : α)
        rfl
      omega
    let gradeFin : s → Fin (N + 1) :=
      fun x ↦ ⟨gradeNat x, Nat.lt_succ_of_le (hgrade_le x)⟩
    have hgrade_injective : Function.Injective gradeFin := by
      intro x y hxy
      exact hgrade_strict.injective (congrArg Fin.val hxy)
    letI : Finite s := Finite.of_injective gradeFin hgrade_injective
    letI : Fintype s := Fintype.ofFinite s
    have hcard_pos : 0 < Fintype.card s := Fintype.card_pos_iff.mpr ⟨⊥⟩
    let m : ℕ := Fintype.card s - 1
    have hm_card : Fintype.card s = m + 1 := by
      dsimp [m]
      exact (Nat.succ_pred_eq_of_pos hcard_pos).symm
    have huniv : (Finset.univ : Finset s).card = m + 1 := by
      simpa using hm_card
    let e₀ : Fin (m + 1) ≃o { x : s // x ∈ (Finset.univ : Finset s) } :=
      (Finset.univ : Finset s).orderIsoOfFin huniv
    let e₁ : { x : s // x ∈ (Finset.univ : Finset s) } ≃o s := by
      refine
        { toFun := fun x ↦ x.1
          invFun := fun x ↦ ⟨x, by simp⟩
          left_inv := ?_
          right_inv := ?_
          map_rel_iff' := ?_ }
      · intro x
        cases x
        rfl
      · intro x
        rfl
      · intro a b
        rfl
    let e : Fin (m + 1) ≃o s := e₀.trans e₁
    have hbot : e 0 = ⊥ := by
      exact e.map_bot
    have htop : e (Fin.last m) = ⊤ := by
      exact e.map_top
    have hstep :
        ∀ i : Fin m, gradeNat (e (Fin.succ i)) = gradeNat (e (Fin.castSucc i)) + 1 := by
      intro i
      have hcov_fin : (Fin.castSucc i : Fin (m + 1)) ⋖ Fin.succ i := by
        have hnat : ((i : ℕ) ⋖ i + 1) := by
          simp
        exact (Fin.covBy_iff).2 hnat
      have hcov_flag : e (Fin.castSucc i) ⋖ e (Fin.succ i) :=
        (apply_covBy_apply_iff e).2 hcov_fin
      have hcov : ((e (Fin.castSucc i) : s) : α) ⋖ ((e (Fin.succ i) : s) : α) := by
        exact (Flag.coe_covBy_coe).2 hcov_flag
      have hcov_grade :
          grade ℤ (e (Fin.castSucc i)) ⋖ grade ℤ (e (Fin.succ i)) := hcov_flag.grade ℤ
      have hbot_left :
          grade ℤ (⊥ : s) ≤ grade ℤ (e (Fin.castSucc i)) := by
        exact grade_mono (bot_le : (⊥ : s) ≤ e (Fin.castSucc i))
      have hbot_right :
          grade ℤ (⊥ : s) ≤ grade ℤ (e (Fin.succ i)) := by
        exact grade_mono (bot_le : (⊥ : s) ≤ e (Fin.succ i))
      rw [Order.covBy_iff_add_one_eq] at hcov_grade
      dsimp [gradeNat]
      omega
    have hindex : ∀ n (hn : n ≤ m), gradeNat (e ⟨n, Nat.lt_succ_of_le hn⟩) = n := by
      intro n hn
      induction n with
      | zero =>
          have hzero : gradeNat (e 0) = 0 := by
            dsimp [gradeNat]
            rw [hbot]
            omega
          simpa using hzero
      | succ n ih =>
          have hn' : n ≤ m := Nat.le_of_succ_le hn
          have hstep' := hstep ⟨n, lt_of_lt_of_le (Nat.lt_succ_self n) hn⟩
          simpa [ih hn'] using hstep'
    have htop_grade : gradeNat (e (Fin.last m)) = N := by
      dsimp [gradeNat, N]
      rw [htop]
      have htop_coe : grade ℤ (⊤ : s) = grade ℤ (⊤ : α) := by
        change grade ℤ ((⊤ : s) : α) = grade ℤ (⊤ : α)
        rfl
      have hbot_coe : grade ℤ (⊥ : s) = grade ℤ (⊥ : α) := by
        change grade ℤ ((⊥ : s) : α) = grade ℤ (⊥ : α)
        rfl
      omega
    have hm_eq_N : m = N := by
      calc
        m = gradeNat (e (Fin.last m)) := by simpa using (hindex m le_rfl).symm
        _ = N := htop_grade
    let p : LTSeries α :=
      { length := m
        toFun := fun i ↦ ((e i : s) : α)
        step := fun i ↦ by
          have : (Fin.castSucc i : Fin (m + 1)) < Fin.succ i := by
            simp
          exact e.strictMono this }
    have hp : (p.length : ℕ) = N := hm_eq_N
    have hdim' : (m : WithBot ℕ∞) ≤ Order.krullDim α := by
      simpa [p] using (Order.LTSeries.length_le_krullDim p)
    have hdim : (N : WithBot ℕ∞) ≤ Order.krullDim α := by
      simpa [hm_eq_N] using hdim'
    simpa [N] using hdim

/-- Helper for Lemma 5.20.2: for comparable irreducible closed subsets, relative codimension is
the difference of the dimension function at their generic points. -/
private theorem codimBetween_eq_toNat_sub_of_irreducible_closeds_le
    [T0Space X] (hδ : IsDimensionFunction δ) {T T' : IrreducibleCloseds X} (hTT' : T ≤ T') :
    codimBetween T T' hTT' =
      Int.toNat
        (δ (Specialization.ofEquiv
            ((irreducible_closeds_equiv_specialization_points (X := X)) T')) -
          δ (Specialization.ofEquiv
            ((irreducible_closeds_equiv_specialization_points (X := X)) T))) := by
  -- Transport the interval of irreducible closed subsets to the generic-point interval and use the
  -- induced integer grading coming from the dimension function.
  letI : GradeOrder ℤ (Specialization X) := hδ.gradeOrder
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  let _ : Fact (e T ≤ e T') := ⟨e.monotone hTT'⟩
  have hconn :
      (Set.range (OrderEmbedding.subtype (Set.Icc (e T) (e T')))).OrdConnected := by
    simpa only [OrderEmbedding.coe_subtype, Subtype.range_coe_subtype] using
      (Set.ordConnected_Icc : (Set.Icc (e T) (e T')).OrdConnected)
  letI : GradeOrder ℤ (Set.Icc (e T) (e T')) :=
    GradeOrder.liftRight (Subtype.val : Set.Icc (e T) (e T') → Specialization X)
      (Subtype.strictMono_coe _)
      (fun x y hxy ↦ by
        exact
          ((Set.OrdConnected.apply_covBy_apply_iff
              (OrderEmbedding.subtype (Set.Icc (e T) (e T'))) hconn).2 hxy))
  apply WithBot.coe_inj.mp
  calc
    (codimBetween T T' hTT' : WithBot ℕ∞) = Order.krullDim (Set.Icc T T') := codimBetween_eq_krullDim hTT'
    _ = Order.krullDim (Set.Icc (e T) (e T')) := by
      exact Order.krullDim_eq_of_orderIso
        (irreducible_closeds_interval_equiv_generic_points (X := X) (T := T) (T' := T'))
    _ = Int.toNat
          (grade ℤ (⊤ : Set.Icc (e T) (e T')) -
            grade ℤ (⊥ : Set.Icc (e T) (e T'))) := by
          exact krullDim_eq_toNat_sub_of_grade_order
    _ = Int.toNat
          (δ (Specialization.ofEquiv (e T')) - δ (Specialization.ofEquiv (e T))) := by
          rfl

-- Proof sketch: use quasi-sobriety together with the derived instance `hδ.t0Space` to identify
-- irreducible closed subsets with closures of their generic points. The dimension-function axioms
-- then compute the common length of maximal chains by telescoping along immediate specializations.
/-- Lemma 5.20.2: if `X` is sober and `δ` is a dimension function on `X`, then `X` is catenary.
Moreover, for any specialization `x ⤳ y`, the difference `δ x - δ y` equals the codimension of
`closure {y}` inside `closure {x}`. Quasi-sobriety is an ambient hypothesis, and `T₀` is derived
canonically from the dimension function. -/
theorem catenarySpace_and_sub_eq_codimBetween_pointClosure
    (hδ : IsDimensionFunction δ)
    :
    CatenarySpace X ∧
      ∀ (x y : X) (hxy : x ⤳ y),
        δ x - δ y =
          (ENat.toNat
            (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
              hxy.toIrreducibleCloseds_le) : ℤ) := by
  letI : T0Space X := hδ.t0Space
  let e : IrreducibleCloseds X ≃o Specialization X :=
    irreducible_closeds_equiv_specialization_points (X := X)
  have hδ_strict :
      StrictMono fun z : Specialization X ↦ δ (Specialization.ofEquiv z) :=
    strictMono_specialization_of_dimensionFunction (δ := δ) hδ
  have hδ_mono :
      Monotone fun z : Specialization X ↦ δ (Specialization.ofEquiv z) := hδ_strict.monotone
  constructor
  · -- The codimension criterion from Lemma 5.11.6 reduces catenarity to finiteness and
    -- additivity of `codimBetween`, both of which follow from the generic-point formula above.
    rw [catenarySpace_iff_finite_codimBetween_and_codimBetween_additive]
    refine ⟨?_, ?_⟩
    · intro T T' hTT'
      rw [codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hTT']
      exact ENat.coe_lt_top _
    · intro T T' T'' hTT' hT'T''
      rw [codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ (hTT'.trans hT'T''),
        codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hTT',
        codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ hT'T'']
      have h01 :
          0 ≤ δ (Specialization.ofEquiv (e T')) - δ (Specialization.ofEquiv (e T)) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone hTT'))
      have h12 :
          0 ≤ δ (Specialization.ofEquiv (e T'')) - δ (Specialization.ofEquiv (e T')) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone hT'T''))
      have h02 :
          0 ≤ δ (Specialization.ofEquiv (e T'')) - δ (Specialization.ofEquiv (e T)) := by
        exact sub_nonneg.mpr (hδ_mono (e.monotone (hTT'.trans hT'T'')))
      have hsumInt :
          (Int.toNat
            (δ (Specialization.ofEquiv (e T'')) -
              δ (Specialization.ofEquiv (e T))) : ℤ) =
            Int.toNat
              (δ (Specialization.ofEquiv (e T')) -
                δ (Specialization.ofEquiv (e T))) +
              Int.toNat
                (δ (Specialization.ofEquiv (e T'')) -
                  δ (Specialization.ofEquiv (e T'))) := by
        rw [Int.toNat_of_nonneg h02, Int.toNat_of_nonneg h01, Int.toNat_of_nonneg h12]
        omega
      have hsum :
          Int.toNat
            (δ (Specialization.ofEquiv (e T'')) -
              δ (Specialization.ofEquiv (e T))) =
            Int.toNat
              (δ (Specialization.ofEquiv (e T')) -
                δ (Specialization.ofEquiv (e T))) +
              Int.toNat
                (δ (Specialization.ofEquiv (e T'')) -
                  δ (Specialization.ofEquiv (e T'))) := by
        exact_mod_cast hsumInt
      exact congrArg (fun n : ℕ ↦ (n : ℕ∞)) hsum
  · intro x y hxy
    -- Specialize the generic-point computation to the interval of point closures.
    have hcodim :
        codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
            hxy.toIrreducibleCloseds_le =
          Int.toNat (δ x - δ y) := by
      have hx :
          Specialization.ofEquiv
              ((irreducible_closeds_equiv_specialization_points (X := X))
                (toIrreducibleCloseds x)) = x := by
        letI : PartialOrder X := specializationOrder X
        change (irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds x) = x
        exact (irreducibleSetEquivPoints (α := X)).right_inv x
      have hy :
          Specialization.ofEquiv
              ((irreducible_closeds_equiv_specialization_points (X := X))
                (toIrreducibleCloseds y)) = y := by
        letI : PartialOrder X := specializationOrder X
        change (irreducibleSetEquivPoints (α := X)) (toIrreducibleCloseds y) = y
        exact (irreducibleSetEquivPoints (α := X)).right_inv y
      simpa [hx, hy] using
        (codimBetween_eq_toNat_sub_of_irreducible_closeds_le (δ := δ) hδ
          hxy.toIrreducibleCloseds_le : _)
    have hnonneg : 0 ≤ δ x - δ y := by
      by_cases hEq : x = y
      · simp [hEq]
      · exact sub_nonneg.mpr (le_of_lt (hδ.strict_of_specializes hxy hEq))
    calc
      δ x - δ y = (Int.toNat (δ x - δ y) : ℤ) := by
        rw [Int.toNat_of_nonneg hnonneg]
      _ = (ENat.toNat
          (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
            hxy.toIrreducibleCloseds_le) : ℤ) := by
        rw [hcodim]
        simp

/-- A quasi-sober topological space with a dimension function is catenary; the ambient `T₀`
structure is derived canonically from the dimension function. -/
theorem catenarySpace (hδ : IsDimensionFunction δ) :
    CatenarySpace X :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.1

-- Proof sketch: this is the codimension component of Lemma 5.20.2, applied to the irreducible
-- closed interval `[closure {y}, closure {x}]`.
/-- On a sober space, a dimension function computes the codimension between point closures along a
specialization. Here quasi-sobriety is ambient, and `T₀` is supplied canonically by the
dimension function. -/
theorem sub_eq_codimBetween_pointClosure (hδ : IsDimensionFunction δ)
    (x y : X) (hxy : x ⤳ y) :
    δ x - δ y =
      (ENat.toNat
        (codimBetween (toIrreducibleCloseds y) (toIrreducibleCloseds x)
          hxy.toIrreducibleCloseds_le) : ℤ) :=
  hδ.catenarySpace_and_sub_eq_codimBetween_pointClosure.2 x y hxy

end

end IsDimensionFunction
