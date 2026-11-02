import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap07.section_7_3.ch7_sec7_3_theorem_7_9

section Lemma712

open Set

/-
Domain sampling for this lemma:
* primary domain: single-coordinate slices of the Section 7.3 single-node flow set
* core/canonical owner: `single_node_flow_set` from Theorem 7.9
* source-facing bridge kept here: the one-step set `T^i` and the validity/tight-point language
  for the source inequality `(7.18)`
-/

/-- The single-coordinate set `T^i` from `(7.17)`, viewed canonically as the `Fin 1`
specialization of the single-node flow set. -/
def one_step_flow_set (a_i : ℝ) : Set ((Fin 1 → ℝ) × (Fin 1 → ℝ)) :=
  single_node_flow_set (fun _ ↦ a_i) (max a_i 0)

/-- Membership in `one_step_flow_set a_i` is exactly the textbook condition
`x_i ∈ {0,1}` and `0 ≤ y_i ≤ a_i x_i`. -/
theorem mem_one_step_flow_set_iff
    {a_i : ℝ} {p : (Fin 1 → ℝ) × (Fin 1 → ℝ)} :
    p ∈ one_step_flow_set a_i ↔
      (p.1 0 = 0 ∨ p.1 0 = 1) ∧
        0 ≤ p.2 0 ∧
          p.2 0 ≤ a_i * p.1 0 := by
  constructor
  · intro hp
    rcases (mem_single_node_flow_set_iff (fun _ ↦ a_i) (max a_i 0) p).mp hp with
      ⟨hx, hy_nonneg, _, hy_le⟩
    simpa using ⟨hx 0, hy_nonneg 0, hy_le 0⟩
  · rintro ⟨hx, hy_nonneg, hy_le⟩
    refine (mem_single_node_flow_set_iff (fun _ ↦ a_i) (max a_i 0) p).mpr ?_
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j
      fin_cases j
      simpa using hx
    · intro j
      fin_cases j
      simpa using hy_nonneg
    · rcases hx with hx | hx
      · rw [hx] at hy_le
        have hy_le_zero : p.2 0 ≤ 0 := by
          simpa using hy_le
        have hzero : p.2 0 = 0 := le_antisymm hy_le_zero hy_nonneg
        simp [hzero]
      · rw [hx] at hy_le
        have hy_le_ai : p.2 0 ≤ a_i := by
          simpa using hy_le
        simpa using hy_le_ai.trans (le_max_left a_i 0)
    · intro j
      fin_cases j
      simpa using hy_le

/-- The source inequality `(7.18)` is valid on `T^i`. -/
def one_step_lifting_valid
    (a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i : ℝ) : Prop :=
  ∀ ⦃p : (Fin 1 → ℝ) × (Fin 1 → ℝ)⦄,
    p ∈ one_step_flow_set a_i →
      α_i * p.2 0 + β_i * p.1 0 ≤ f_i (p.2 0)

/-- Expanding `one_step_lifting_valid a_i f_i α_i β_i` recovers validity of `(7.18)` on
`T^i`. -/
theorem one_step_lifting_valid_iff
    {a_i : ℝ} {f_i : ℝ → ℝ} {α_i β_i : ℝ} :
    one_step_lifting_valid a_i f_i α_i β_i ↔
      ∀ ⦃p : (Fin 1 → ℝ) × (Fin 1 → ℝ)⦄,
        p ∈ one_step_flow_set a_i →
          α_i * p.2 0 + β_i * p.1 0 ≤ f_i (p.2 0) :=
  Iff.rfl

/-- A point `y_i ∈ [0, a_i]` where the affine minorant from `(7.18)` is tight against `f_i`. -/
def one_step_lifting_tight_point
    (a_i : ℝ) (f_i : ℝ → ℝ) (α_i β_i : ℝ) (y_i : ℝ) : Prop :=
  y_i ∈ Icc (0 : ℝ) a_i ∧ α_i * y_i + β_i = f_i y_i

/-- Lemma 7.12 (1). Assuming only `0 ≤ f_i(0)`, validity of `(7.18)` on `T^i` is equivalent to
the interval condition `α_i y_i + β_i ≤ f_i(y_i)` for all `y_i ∈ [0, a_i]`. -/
theorem lemma_7_12_valid_iff_interval_condition
    {a_i : ℝ} {f_i : ℝ → ℝ} {α_i β_i : ℝ}
    (hf_i_zero_nonneg : 0 ≤ f_i 0) :
    one_step_lifting_valid a_i f_i α_i β_i ↔
      ∀ y_i ∈ Icc (0 : ℝ) a_i, α_i * y_i + β_i ≤ f_i y_i := by
  constructor
  · intro hvalid y_i hy_i
    let p : (Fin 1 → ℝ) × (Fin 1 → ℝ) := (fun _ ↦ 1, fun _ ↦ y_i)
    have hp : p ∈ one_step_flow_set a_i := by
      rw [mem_one_step_flow_set_iff]
      change ((1 : ℝ) = 0 ∨ (1 : ℝ) = 1) ∧ 0 ≤ y_i ∧ y_i ≤ a_i * 1
      refine ⟨Or.inr rfl, hy_i.1, ?_⟩
      simpa using hy_i.2
    simpa [p] using hvalid hp
  · intro hinterval p hp
    rcases (mem_one_step_flow_set_iff.mp hp) with ⟨hx, hy_nonneg, hy_le⟩
    rcases hx with hx | hx
    · rw [hx] at hy_le
      have hy_le_zero : p.2 0 ≤ 0 := by
        simpa using hy_le
      have hy_zero : p.2 0 = 0 := le_antisymm hy_le_zero hy_nonneg
      rw [hx, hy_zero]
      simpa using hf_i_zero_nonneg
    · rw [hx] at hy_le
      rw [hx]
      simpa using hinterval (p.2 0) ⟨hy_nonneg, by simpa using hy_le⟩

/-- Lemma 7.12 (2). The additional source side condition in the facet criterion for `(7.18)` is
exactly the existence of two distinct points of `[0, a_i]` where the affine minorant is tight
against `f_i`. -/
theorem lemma_7_12_two_distinct_tight_points_iff
    {a_i : ℝ} {f_i : ℝ → ℝ} {α_i β_i : ℝ} :
    (∃ y_i' y_i'',
        y_i' ≠ y_i'' ∧
          one_step_lifting_tight_point a_i f_i α_i β_i y_i' ∧
            one_step_lifting_tight_point a_i f_i α_i β_i y_i'') ↔
      ∃ y_i' ∈ Icc (0 : ℝ) a_i,
        ∃ y_i'' ∈ Icc (0 : ℝ) a_i,
          y_i' ≠ y_i'' ∧
            α_i * y_i' + β_i = f_i y_i' ∧
              α_i * y_i'' + β_i = f_i y_i'' := by
  constructor
  · rintro ⟨y_i', y_i'', hne, ⟨hy_i', hEq_i'⟩, ⟨hy_i'', hEq_i''⟩⟩
    exact ⟨y_i', hy_i', y_i'', hy_i'', hne, hEq_i', hEq_i''⟩
  · rintro ⟨y_i', hy_i', y_i'', hy_i'', hne, hEq_i', hEq_i''⟩
    exact ⟨y_i', y_i'', hne, ⟨hy_i', hEq_i'⟩, ⟨hy_i'', hEq_i''⟩⟩

end Lemma712
