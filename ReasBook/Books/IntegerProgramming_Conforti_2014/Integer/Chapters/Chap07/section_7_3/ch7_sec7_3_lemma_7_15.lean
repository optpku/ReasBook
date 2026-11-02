import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_12
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_14
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_lemma_7_13.LiftingFunction

noncomputable section

section Lemma715

/-- The candidate values in the recursive update `(7.19)` that produces the next source function
from the previous stage by optimizing over the one-step flow set. -/
def flow_cover_recursive_lifting_step_values
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i z : ℝ) : Set ℝ :=
  {v | ∃ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
      p ∈ one_step_flow_set a_i ∧
        z + p.2 0 ∈ Set.Icc (0 : ℝ) b ∧
          v = f_i (z + p.2 0) - (α_i * p.2 0 + β_i * p.1 0)}

/-- Membership in `flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z` is exactly the
optimization relation appearing in `(7.19)`. -/
@[simp] theorem mem_flow_cover_recursive_lifting_step_values_iff
    {b a_i : ℝ} {f_i : ℝ → ℝ} {α_i β_i z v : ℝ} :
    v ∈ flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z ↔
      ∃ p : (Fin 1 → ℝ) × (Fin 1 → ℝ),
        p ∈ one_step_flow_set a_i ∧
          z + p.2 0 ∈ Set.Icc (0 : ℝ) b ∧
            v = f_i (z + p.2 0) - (α_i * p.2 0 + β_i * p.1 0) :=
  Iff.rfl

/-- The recursive update `(7.19)` sending `f_i` to the next function. -/
noncomputable def flow_cover_recursive_lifting_step
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i : ℝ) (z : ℝ) : ℝ :=
  sInf (flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z)

/-- Expanding `flow_cover_recursive_lifting_step` recovers the infimum formula from `(7.19)`. -/
theorem flow_cover_recursive_lifting_step_eq
    (b a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i z : ℝ) :
    flow_cover_recursive_lifting_step b a_i f_i α_i β_i z =
      sInf (flow_cover_recursive_lifting_step_values b a_i f_i α_i β_i z) :=
  rfl

/-- The stage-indexed recursive functions from `(7.19)`, rooted at the canonical flow-cover
lifting function. The stage `0` term is the source function `f`, and stage `k + 1` is obtained by
applying `(7.19)` with the coefficient triple indexed by `k`. -/
noncomputable def flow_cover_recursive_lifting_function
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ) (i : ℕ) : ℝ → ℝ :=
  Nat.rec
    (flow_cover_lifting_function
      b
      (flow_cover_excess coverCapacity b Finset.univ)
      coverCapacity)
    (fun k f_k ↦
      if hk : k < m then
        flow_cover_recursive_lifting_step
          b
          (liftCapacity ⟨k, hk⟩)
          f_k
          (α ⟨k, hk⟩)
          (β ⟨k, hk⟩)
      else
        f_k)
    i

/-- Stage `0` of the recursive family `(7.19)` is the canonical flow-cover lifting function. -/
@[simp] theorem flow_cover_recursive_lifting_function_zero
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β 0 =
      flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity :=
  rfl

/-- When `k < m`, the recursive family satisfies the one-step update formula `(7.19)` at stage
`k + 1`. -/
theorem flow_cover_recursive_lifting_function_succ
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    {k : ℕ} (hk : k < m) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β (k + 1) =
      flow_cover_recursive_lifting_step
        b
        (liftCapacity ⟨k, hk⟩)
        (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
        (α ⟨k, hk⟩)
        (β ⟨k, hk⟩) := by
  simp [flow_cover_recursive_lifting_function, hk]

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_lemma_7_15.lean: the zero one-step pair is feasible
for every one-step capacity. -/
lemma zero_mem_one_step_flow_set (a_i : ℝ) :
    ((fun _ : Fin 1 ↦ (0 : ℝ)), fun _ : Fin 1 ↦ (0 : ℝ)) ∈ one_step_flow_set a_i := by
  -- The zero pair satisfies each coordinate condition in the one-step membership criterion.
  rw [mem_one_step_flow_set_iff]
  refine ⟨Or.inl rfl, le_rfl, ?_⟩
  simp

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_lemma_7_15.lean: a recursive one-step update
preserves agreement with a superadditive reference function on `Set.Icc 0 b`. -/
lemma flowCoverRecursiveLiftingStep_eq_of_eqOn
    {b a_i : ℝ} {f g : ℝ → ℝ} {α_i β_i z : ℝ}
    (hsuper : SequenceIndependentLifting.is_superadditive_on_Icc f b)
    (heq : Set.EqOn g f (Set.Icc (0 : ℝ) b))
    (hvalid : one_step_lifting_valid a_i g α_i β_i)
    (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_recursive_lifting_step b a_i g α_i β_i z = f z := by
  -- Every candidate dominates `f z`: validity removes its affine cost, and
  -- superadditivity separates the resulting reference value at `z + p.2 0`.
  have hlower :
      ∀ v ∈ flow_cover_recursive_lifting_step_values b a_i g α_i β_i z, f z ≤ v := by
    intro v hv
    rcases mem_flow_cover_recursive_lifting_step_values_iff.mp hv with
      ⟨p, hp, hz_add, rfl⟩
    rcases mem_one_step_flow_set_iff.mp hp with ⟨_, hy_nonneg, _⟩
    have hy : p.2 0 ∈ Set.Icc (0 : ℝ) b := by
      constructor
      · exact hy_nonneg
      · linarith [hz.1, hz_add.2]
    have hseparate : f z ≤ f (z + p.2 0) - f (p.2 0) := by
      linarith [hsuper hz hy hz_add]
    calc
      f z ≤ f (z + p.2 0) - f (p.2 0) := hseparate
      _ = g (z + p.2 0) - g (p.2 0) := by rw [heq hz_add, heq hy]
      _ ≤ g (z + p.2 0) - (α_i * p.2 0 + β_i * p.1 0) := by
        linarith [hvalid hp]
  have hbdd : BddBelow (flow_cover_recursive_lifting_step_values b a_i g α_i β_i z) :=
    ⟨f z, hlower⟩
  -- The zero pair realizes exactly `f z`, so the infimum also lies below `f z`.
  have hf_mem : f z ∈ flow_cover_recursive_lifting_step_values b a_i g α_i β_i z := by
    refine mem_flow_cover_recursive_lifting_step_values_iff.mpr ?_
    refine ⟨((fun _ : Fin 1 ↦ (0 : ℝ)), fun _ : Fin 1 ↦ (0 : ℝ)),
      zero_mem_one_step_flow_set a_i, ?_, ?_⟩
    · simpa using hz
    · simpa using (heq hz).symm
  have hnonempty :
      (flow_cover_recursive_lifting_step_values b a_i g α_i β_i z).Nonempty :=
    ⟨f z, hf_mem⟩
  rw [flow_cover_recursive_lifting_step_eq]
  exact le_antisymm (csInf_le hbdd hf_mem) (le_csInf hnonempty hlower)

/-- Helper for remote integer-programming sorry cleanup
Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_lemma_7_15.lean: every recursive stage up to `m`
agrees on `Set.Icc 0 b` with the canonical flow-cover lifting function. -/
lemma flowCoverRecursiveLiftingFunction_eq_of_le
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    (hsuper :
      SequenceIndependentLifting.is_superadditive_on_Icc
        (flow_cover_lifting_function
          b
          (flow_cover_excess coverCapacity b Finset.univ)
          coverCapacity)
        b)
    (hvalid :
      ∀ i : Fin m,
        one_step_lifting_valid
          (liftCapacity i)
          (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i)
          (α i)
          (β i))
    {k : ℕ} (hk : k ≤ m) :
    Set.EqOn
      (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β k)
      (flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity)
      (Set.Icc (0 : ℝ) b) := by
  -- Induct over the stage while retaining the bound needed to form its `Fin m` index.
  induction k with
  | zero =>
      intro z hz
      simp only [flow_cover_recursive_lifting_function_zero]
  | succ k ih =>
      have hklt : k < m := Nat.lt_of_succ_le hk
      have hk_le : k ≤ m := Nat.le_of_lt hklt
      intro z hz
      rw [flow_cover_recursive_lifting_function_succ b coverCapacity liftCapacity α β hklt]
      exact
        flowCoverRecursiveLiftingStep_eq_of_eqOn
          hsuper (ih hk_le) (hvalid ⟨k, hklt⟩) hz

/-- remote integer-programming sorry cleanup Integer/Chapters/Chap07/section_7_3/ch7_sec7_3_lemma_7_15.lean.
Lemma 7.15. Let `f` be the canonical
flow-cover lifting function from Lemmas 7.13 and 7.14 for nonnegative cover capacities whose full
support is a flow cover, and let
`flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i` be the stage `i`
function defined recursively by `(7.19)`. If each one-step pair `(α_i, β_i)` is valid on the
corresponding one-step flow set, then every recursive stage coincides with `f` on
`0 ≤ z ≤ b`. -/
theorem flow_cover_recursive_lifting_eq_lifting_function
    {t m : ℕ} (b : ℝ) (coverCapacity : Fin t → ℝ)
    (liftCapacity α β : Fin m → ℝ)
    (hcover_nonneg : ∀ j, 0 ≤ coverCapacity j)
    (hcover : IsFlowCover coverCapacity b Finset.univ)
    (hvalid :
      ∀ i : Fin m,
        one_step_lifting_valid
          (liftCapacity i)
          (flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i)
          (α i)
          (β i))
    (i : Fin (m + 1)) {z : ℝ} (hz : z ∈ Set.Icc (0 : ℝ) b) :
    flow_cover_recursive_lifting_function b coverCapacity liftCapacity α β i z =
      flow_cover_lifting_function
        b
        (flow_cover_excess coverCapacity b Finset.univ)
        coverCapacity z := by
  -- Lemma 7.14 supplies the invariant's superadditive reference function.
  have hsuper :=
    flow_cover_lifting_function_is_superadditive_on_Icc
      b coverCapacity hcover_nonneg hcover
  have hi : i.val ≤ m := Nat.lt_succ_iff.mp i.isLt
  -- Specialize the bounded-stage invariant at the requested `Fin (m + 1)` stage and point.
  exact
    flowCoverRecursiveLiftingFunction_eq_of_le
      b coverCapacity liftCapacity α β hsuper hvalid hi hz

end Lemma715
