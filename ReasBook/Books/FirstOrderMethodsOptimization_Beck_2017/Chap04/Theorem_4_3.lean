/-
Authors: Shu Miao, Zhiyan Wang, Suwan Wu, Changyu Zou, Xinyi Guo, Yunxi Duan, Wanli Ma, Zichen Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: optpku/ReasBook@f9674e6420188b5921fdbff7917aaf0e10cfa8a0:ReasBook/Books/FirstOrderMethodsOptimization_Beck_2017/README.md (Contributors).
-/

import FirstOrderMethodsOptimization_Beck_2017.Chap02.Definition_2_5
import FirstOrderMethodsOptimization_Beck_2017.Chap04.Definition_4_1

-- Declarations for this item will be appended below by the statement pipeline.

open Matrix
open scoped BigOperators

universe u

section

variable {p : ℕ}
variable {E : Fin p → Type u}
variable [∀ i, AddCommGroup (E i)]
variable [∀ i, Module ℝ (E i)]

/- Theorem 4.3 uses a finite-product induction. The helper API below isolates the `EReal`
order step and the head/tail normalization so the main theorem can stay close to the textbook
separation argument. -/

/-- Helper for Theorem 4.3: a finite sum of `EReal` terms stays away from `⊥` if each summand
stays away from `⊥`. -/
lemma finset_ereal_sum_ne_bot {κ : Type*} (s : Finset κ) (φ : κ → EReal)
    (hφ : ∀ i ∈ s, φ i ≠ ⊥) :
    s.sum φ ≠ ⊥ := by
  -- Reduce `∑ i in s, φ i = ⊥` to the impossible claim that one summand equals `⊥`.
  intro hsum
  rcases WithBot.sum_eq_bot_iff.mp hsum with ⟨i, hi, hbot⟩
  exact hφ i hi hbot

/-- Helper for Theorem 4.3: the sum of two indexed suprema in `EReal` is the supremum over the
product index of the pointwise sums. -/
private lemma ereal_iSup_add_eq_iSup_prod {α β : Type*} (u : α → EReal) (v : β → EReal) :
    (⨆ a, u a) + ⨆ b, v b = ⨆ p : α × β, u p.1 + v p.2 := by
  refine le_antisymm ?_ ?_
  · -- For the reverse inequality, approximate each `iSup` from below and choose matching
    -- witnesses in the product index.
    refine EReal.add_le_of_forall_lt ?_
    intro a ha b hb
    rcases lt_iSup_iff.mp ha with ⟨i, hi⟩
    rcases lt_iSup_iff.mp hb with ⟨j, hj⟩
    exact (add_le_add hi.le hj.le).trans (le_iSup_of_le (i, j) le_rfl)
  · -- The upper bound is the pointwise monotonicity of addition under `iSup`.
    refine iSup_le ?_
    intro p
    exact add_le_add (le_iSup u p.1) (le_iSup v p.2)

/-- Helper for Theorem 4.3: on `Fin (n + 1)`, the affine perturbation defining the conjugate of a
separable sum splits into the head coordinate term plus the tail-block perturbation. -/
lemma fin_succ_affine_term_eq_head_add_tail
    {n : ℕ} {E : Fin (n + 1) → Type u}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (f : ∀ i, E i → EReal) (h_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (y : ∀ i, Module.Dual ℝ (E i)) (x : ∀ i, E i) :
    (((LinearMap.lsum ℝ E ℝ y) x : ℝ) : EReal) - ∑ i, f i (x i) =
      ((y 0 (x 0) : EReal) - f 0 (x 0)) +
        ((((LinearMap.lsum ℝ (fun i : Fin n ↦ E i.succ) ℝ (fun i ↦ y i.succ))
            (fun i ↦ x i.succ) : ℝ) : EReal) -
          ∑ i : Fin n, f i.succ (x i.succ)) := by
  -- The tail sum inherits the no-`⊥` property from properness, so `EReal.neg_add` is safe.
  have htail_ne_bot : (∑ i : Fin n, f i.succ (x i.succ)) ≠ ⊥ := by
    simpa using
      (finset_ereal_sum_ne_bot Finset.univ (fun i : Fin n ↦ f i.succ (x i.succ)) fun i hi ↦
        (h_proper i.succ).ne_bot (x i.succ))
  have hlin :
      (((LinearMap.lsum ℝ E ℝ y) x : ℝ) : EReal) =
        (y 0 (x 0) : EReal) +
          (((LinearMap.lsum ℝ (fun i : Fin n ↦ E i.succ) ℝ (fun i ↦ y i.succ))
              (fun i ↦ x i.succ) : ℝ) : EReal) := by
    -- `LinearMap.lsum` evaluates to the head dual pairing plus the tail pairing sum.
    simp [LinearMap.lsum_apply, Fin.sum_univ_succ, EReal.coe_add]
  have hsum :
      (∑ i, f i (x i)) = f 0 (x 0) + ∑ i : Fin n, f i.succ (x i.succ) := by
    simpa using (Fin.sum_univ_succ (fun i : Fin (n + 1) ↦ f i (x i)))
  -- Rewrite both the linear pairing and the separable sum into head-plus-tail normal form.
  rw [hlin, hsum, sub_eq_add_neg]
  rw [EReal.neg_add (.inl ((h_proper 0).ne_bot (x 0))) (.inr htail_ne_bot)]
  -- After the normalization, the result is just reassociation of addition.
  simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]

/-- Helper for Theorem 4.3: the conjugate of the `(n + 1)`-block separable sum splits into the
head conjugate plus the conjugate of the tail separable sum. -/
lemma conjugate_function_separable_sum_finSucc
    {n : ℕ} {E : Fin (n + 1) → Type u}
    [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]
    (f : ∀ i, E i → EReal) (h_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (y : ∀ i, Module.Dual ℝ (E i)) :
    conjugate_function (fun x : ∀ i, E i ↦ ∑ i, f i (x i)) (LinearMap.lsum ℝ E ℝ y) =
      conjugate_function (f 0) (y 0) +
        conjugate_function
          (fun x : ∀ i : Fin n, E i.succ ↦ ∑ i, f i.succ (x i))
          (LinearMap.lsum ℝ (fun i : Fin n ↦ E i.succ) ℝ (fun i ↦ y i.succ)) := by
  let fullObj : (∀ i, E i) → EReal :=
    fun x ↦ (((LinearMap.lsum ℝ E ℝ y) x : ℝ) : EReal) - ∑ i, f i (x i)
  let headObj : E 0 → EReal := fun x0 ↦ (y 0 x0 : EReal) - f 0 x0
  let tailObj : (∀ i : Fin n, E i.succ) → EReal :=
    fun x ↦
      (((LinearMap.lsum ℝ (fun i : Fin n ↦ E i.succ) ℝ (fun i ↦ y i.succ)) x : ℝ) : EReal) -
        ∑ i, f i.succ (x i)
  let splitObj : E 0 × (∀ i : Fin n, E i.succ) → EReal :=
    fun p ↦ headObj p.1 + tailObj p.2
  -- Transport the full attainable-value range to the image of head and tail attainable values
  -- under addition.
  have hrange :
      Set.range fullObj = Set.image2 (· + ·) (Set.range headObj) (Set.range tailObj) := by
    ext z
    constructor
    · rintro ⟨x, rfl⟩
      refine ⟨headObj (x 0), ⟨x 0, rfl⟩, tailObj (fun i ↦ x i.succ), ⟨fun i ↦ x i.succ, rfl⟩, ?_⟩
      -- The head/tail affine normalization identifies the full value with the sum of the two
      -- coordinatewise perturbations.
      simpa [fullObj, headObj, tailObj] using
        (fin_succ_affine_term_eq_head_add_tail f h_proper y x).symm
    · rintro ⟨a, ⟨x0, rfl⟩, b, ⟨xtail, rfl⟩, rfl⟩
      refine ⟨Fin.cons x0 xtail, ?_⟩
      -- Reassemble a full vector from its head and tail coordinates and reuse the same
      -- normalization lemma in the opposite direction.
      simpa [fullObj, headObj, tailObj] using
        fin_succ_affine_term_eq_head_add_tail f h_proper y (Fin.cons x0 xtail)
  have hsplitRange :
      Set.image2 (· + ·) (Set.range headObj) (Set.range tailObj) = Set.range splitObj := by
    ext z
    constructor
    · rintro ⟨a, ⟨x0, rfl⟩, b, ⟨xtail, rfl⟩, rfl⟩
      exact ⟨(x0, xtail), rfl⟩
    · rintro ⟨⟨x0, xtail⟩, rfl⟩
      exact ⟨headObj x0, ⟨x0, rfl⟩, tailObj xtail, ⟨xtail, rfl⟩, rfl⟩
  -- Once the range is separated, the only remaining step is the `EReal` supremum identity over
  -- the product index.
  rw [conjugate_function_apply, conjugate_function_apply, conjugate_function_apply]
  rw [hrange, hsplitRange, sSup_range, sSup_range, sSup_range]
  simpa [splitObj, headObj, tailObj, iSup_prod'] using
    (ereal_iSup_add_eq_iSup_prod headObj tailObj).symm

/- Theorem 4.3 is a `bridge/view` item in convex conjugacy: its source-facing content is the
separable-sum conjugacy formula, while the product-dual map itself is already owned canonically by
mathlib's Pi linear-map API as `LinearMap.lsum`. The primitive data are the coordinate dual vectors
`y`; the product dual they determine is derived from that owner abstraction and should not be
duplicated locally. -/

-- Proof sketch: unfold `conjugate_function` for the product-space sum and rewrite the pairing with
-- `LinearMap.lsum_apply`; evaluating the resulting sum of composed projections gives
-- `∑ i, y i (x i)`. The supremum then separates into independent coordinatewise suprema, which are
-- exactly the values of the individual conjugates.
/-- Theorem 4.3: if each coordinate function is proper, then the conjugate of the
finite separable sum on the product space, evaluated at the canonical product dual
`LinearMap.lsum ℝ E ℝ y` determined by the coordinate dual vectors, is the sum of the
coordinatewise conjugates. -/
theorem conjugate_function_separable_sum_eq_sum_conjugate_function
    (f : ∀ i, E i → EReal) (h_proper : ∀ i, IsProperExtendedRealFunction (f i))
    (y : ∀ i, Module.Dual ℝ (E i)) :
    conjugate_function (fun x : ∀ i, E i ↦ ∑ i, f i (x i)) (LinearMap.lsum ℝ E ℝ y) =
      ∑ i, conjugate_function (f i) (y i) := by
  -- Induct on the number of coordinates, using the head/tail split to match the textbook proof.
  revert y h_proper f
  induction p with
  | zero =>
      intro f h_proper y
      -- In the empty product, the objective and the conjugate sum are both the empty sum `0`.
      simp [conjugate_function_apply]
  | succ n ih =>
      intro f h_proper y
      -- Separate the first block from the tail and then apply the inductive hypothesis to the
      -- tail family.
      rw [conjugate_function_separable_sum_finSucc f h_proper y, Fin.sum_univ_succ]
      rw [ih (E := fun i : Fin n ↦ E i.succ)
        (fun i : Fin n ↦ f i.succ)
        (fun i : Fin n ↦ h_proper i.succ)
        (fun i : Fin n ↦ y i.succ)]

section

variable {ι : Type u} [Fintype ι] [DecidableEq ι]

/-- Companion bridge: on a finite real coordinate space `ι → ℝ`, the product dual obtained from
the coordinate functionals `LinearMap.toSpanSingleton ℝ ℝ (y i)` is exactly the Euclidean pairing
dual `dotProductEquiv ℝ ι y`. -/
theorem lsum_toSpanSingleton_eq_dotProductEquiv (y : ι → ℝ) :
    LinearMap.lsum ℝ (fun _ : ι ↦ ℝ) ℝ
        (fun i ↦ LinearMap.toSpanSingleton ℝ ℝ (y i)) =
      dotProductEquiv ℝ ι y := by
  ext x
  simp [LinearMap.lsum_apply, dotProductEquiv, dotProduct, mul_comm]

end

end
