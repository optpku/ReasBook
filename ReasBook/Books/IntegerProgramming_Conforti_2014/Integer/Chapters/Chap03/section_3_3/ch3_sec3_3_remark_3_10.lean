/-
Authors: Ziyu Wang
Released under Apache 2.0 license as described in the file LICENSE.
Project-level attribution: TropicalFatFish/ReasBook-integer-programming@cd8690514e91159fccb6bfdf14ab167259196471:ReasBook/Books/IntegerProgramming_Conforti_2014/README.md (Confirmed formalization attribution).
Attribution scope: project formalization lead, confirmed by the submitter on 2026-11-04.
-/

import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_4
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_2.ch3_sec3_2_theorem_3_5
import IntegerProgramming_Conforti_2014.Integer.Chapters.Chap03.section_3_3.ch3_sec3_3_definition_3_3_extra_1

open scoped Matrix

/-- Helper for Remark 3.10: every primal-feasible/dual-feasible pair satisfies weak duality. -/
lemma weak_duality_feasible_pair
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    {x : Fin n → ℝ}
    {u : Fin m → ℝ}
    (hx : x ∈ primal_feasible_region A b)
    (hu : u ∈ dual_feasible_region A c) :
    c ⬝ᵥ x ≤ u ⬝ᵥ b := by
  rcases (mem_primal_feasible_region_iff A b x).mp hx with hx_feas
  rcases (mem_dual_feasible_region_iff A c u).mp hu with ⟨hu_eq, hu_nonneg⟩
  -- Rewrite the primal value through the dual equality and compare rowwise.
  calc
    c ⬝ᵥ x = (u ᵥ* A) ⬝ᵥ x := by rw [hu_eq]
    _ = u ⬝ᵥ (A *ᵥ x) := by rw [Matrix.dotProduct_mulVec]
    _ ≤ u ⬝ᵥ b := dotProduct_le_dotProduct_of_nonneg_left hx_feas hu_nonneg

/-- Helper for Remark 3.10: a dual feasible point gives a global upper bound on all primal
objective values. -/
lemma primal_objective_values_bddAbove_of_dual_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    BddAbove (primal_objective_values A b c) := by
  rcases hD with ⟨u, hu⟩
  refine ⟨u ⬝ᵥ b, ?_⟩
  rintro z ⟨x, hx, rfl⟩
  exact weak_duality_feasible_pair A b c hx hu

/-- Helper for Remark 3.10: the dual feasible region is nonempty exactly when every primal
recession direction has nonpositive objective slope. -/
lemma dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    Set.Nonempty (dual_feasible_region A c) ↔
      ∀ y : Fin n → ℝ, A *ᵥ y ≤ 0 → c ⬝ᵥ y ≤ 0 := by
  simpa [dual_feasible_region, Matrix.mulVec_transpose, Matrix.vecMul_transpose, dotProduct_comm]
    using feasible_nonnegative_linear_system_iff_nonpositive_row_multipliers Aᵀ c

/-- Helper for Remark 3.10: a feasible point together with a recession direction of positive
objective slope forces the primal objective set to be unbounded above. -/
lemma primal_objective_values_not_bddAbove_of_improving_direction
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    {y : Fin n → ℝ}
    (hyA : A *ᵥ y ≤ 0)
    (hyc : 0 < c ⬝ᵥ y) :
    ¬ BddAbove (primal_objective_values A b c) := by
  rcases hP with ⟨x₀, hx₀⟩
  have hx₀_feas := (mem_primal_feasible_region_iff A b x₀).mp hx₀
  intro hbounded
  rcases hbounded with ⟨M, hM⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (M - c ⬝ᵥ x₀) / (c ⬝ᵥ y) < N := by
    exact exists_nat_gt ((M - c ⬝ᵥ x₀) / (c ⬝ᵥ y))
  have hNmul : M - c ⬝ᵥ x₀ < (N : ℝ) * (c ⬝ᵥ y) := by
    exact (div_lt_iff₀ hyc).mp hN
  have hN' : M < c ⬝ᵥ x₀ + (N : ℝ) * (c ⬝ᵥ y) := by
    linarith
  let xN : Fin n → ℝ := x₀ + (N : ℝ) • y
  have hxN : xN ∈ primal_feasible_region A b := by
    rw [mem_primal_feasible_region_iff]
    intro i
    have hyi : (N : ℝ) * (A *ᵥ y) i ≤ 0 := by
      have hNnonneg : 0 ≤ (N : ℝ) := by
        exact_mod_cast Nat.zero_le N
      exact mul_nonpos_of_nonneg_of_nonpos hNnonneg (hyA i)
    calc
      (A *ᵥ xN) i = (A *ᵥ x₀) i + (N : ℝ) * (A *ᵥ y) i := by
        simp [xN, Matrix.mulVec_add, Matrix.mulVec_smul]
      _ ≤ b i + 0 := by
        nlinarith [hx₀_feas i, hyi]
      _ = b i := by
        ring
  have hxN_value : M < c ⬝ᵥ xN := by
    calc
      M < c ⬝ᵥ x₀ + (N : ℝ) * (c ⬝ᵥ y) := hN'
      _ = c ⬝ᵥ xN := by
        simp [xN, dotProduct_add, dotProduct_smul]
  exact (not_lt_of_ge (hM ⟨xN, hxN, rfl⟩)) hxN_value

/-- Helper for Remark 3.10: when the primal region is nonempty, primal unboundedness is equivalent
to the dual feasible region being empty. -/
theorem primal_objective_unbounded_iff_dual_feasible_region_empty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b)) :
    ¬ BddAbove (primal_objective_values A b c) ↔
      dual_feasible_region A c = (∅ : Set (Fin m → ℝ)) := by
  classical
  constructor
  · intro hunbounded
    by_contra hD
    have hDnonempty : Set.Nonempty (dual_feasible_region A c) := by
      rw [← Set.not_nonempty_iff_eq_empty] at hD
      exact not_not.mp hD
    exact hunbounded (primal_objective_values_bddAbove_of_dual_nonempty A b c hDnonempty)
  · intro hD
    have hDempty : ¬ Set.Nonempty (dual_feasible_region A c) := by
      rwa [Set.not_nonempty_iff_eq_empty]
    have hnotforall :
        ¬ ∀ y : Fin n → ℝ, A *ᵥ y ≤ 0 → c ⬝ᵥ y ≤ 0 := by
      intro hforall
      exact hDempty
        ((dual_feasible_region_nonempty_iff_nonpositive_on_recession_directions A c).2 hforall)
    rcases not_forall.mp hnotforall with ⟨y, hy⟩
    rcases Classical.not_imp.mp hy with ⟨hyA, hyc⟩
    exact primal_objective_values_not_bddAbove_of_improving_direction A b c hP hyA
      (lt_of_not_ge hyc)

/-- Helper for Remark 3.10: the linear system encoding `c ⬝ᵥ x ≥ z` together with `A *ᵥ x ≤ b`. -/
def objective_threshold_matrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) :
    Matrix (Fin (m + 1)) (Fin n) ℝ
  | ⟨0, _⟩, j => -c j
  | ⟨i + 1, hi⟩, j => A ⟨i, Nat.lt_of_succ_lt_succ hi⟩ j

/-- Helper for Remark 3.10: the zeroth row of the threshold matrix is `-c`. -/
@[simp] lemma objective_threshold_matrix_zero
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (j : Fin n) :
    objective_threshold_matrix A c 0 j = -c j := rfl

/-- Helper for Remark 3.10: every successor row of the threshold matrix is a row of `A`. -/
@[simp] lemma objective_threshold_matrix_succ
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (i : Fin m)
    (j : Fin n) :
    objective_threshold_matrix A c i.succ j = A i j := by
  rcases i with ⟨i, hi⟩
  rfl

/-- Helper for Remark 3.10: the right-hand side of the threshold system with level `z`. -/
def objective_threshold_rhs
    {m : ℕ}
    (b : Fin m → ℝ)
    (z : ℝ) :
    Fin (m + 1) → ℝ
  | ⟨0, _⟩ => -z
  | ⟨i + 1, hi⟩ => b ⟨i, Nat.lt_of_succ_lt_succ hi⟩

/-- Helper for Remark 3.10: the zeroth right-hand-side entry of the threshold system is `-z`. -/
@[simp] lemma objective_threshold_rhs_zero
    {m : ℕ}
    (b : Fin m → ℝ)
    (z : ℝ) :
    objective_threshold_rhs b z 0 = -z := rfl

/-- Helper for Remark 3.10: every successor right-hand-side entry of the threshold system comes
from `b`. -/
@[simp] lemma objective_threshold_rhs_succ
    {m : ℕ}
    (b : Fin m → ℝ)
    (z : ℝ)
    (i : Fin m) :
    objective_threshold_rhs b z i.succ = b i := by
  rcases i with ⟨i, hi⟩
  rfl

/-- Helper for Remark 3.10: the threshold system row multiplier decomposes into the coefficient
on the objective row and the tail multiplier on the original rows. -/
lemma vecMul_objective_threshold_matrix
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ)
    (y : Fin (m + 1) → ℝ) :
    y ᵥ* objective_threshold_matrix A c =
      fun j ↦ -y 0 * c j + ((fun i : Fin m ↦ y i.succ) ᵥ* A) j := by
  ext j
  have hsplit :
      (y ᵥ* objective_threshold_matrix A c) j =
        y 0 * objective_threshold_matrix A c 0 j +
          ∑ i : Fin m, y i.succ * objective_threshold_matrix A c i.succ j := by
    rw [Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  rw [hsplit]
  simp [Matrix.vecMul, dotProduct]

/-- Helper for Remark 3.10: the threshold-system right-hand side splits into the objective-row
contribution and the original right-hand side. -/
lemma dotProduct_objective_threshold_rhs
    {m : ℕ}
    (b : Fin m → ℝ)
    (z : ℝ)
    (y : Fin (m + 1) → ℝ) :
    y ⬝ᵥ objective_threshold_rhs b z =
      -y 0 * z + (fun i : Fin m ↦ y i.succ) ⬝ᵥ b := by
  have hsplit :
      y ⬝ᵥ objective_threshold_rhs b z =
        y 0 * objective_threshold_rhs b z 0 +
          ∑ i : Fin m, y i.succ * objective_threshold_rhs b z i.succ := by
    rw [dotProduct, Fin.sum_univ_succ]
  rw [hsplit]
  simp [dotProduct]

/-- Helper for Remark 3.10: if a real threshold lies strictly above the primal extended supremum,
then some dual-feasible point has objective value strictly below that threshold. -/
lemma exists_dual_feasible_below_of_lt_primal_sup
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    {z : ℝ}
    (hz :
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region A b) <
        (z : EReal)) :
    ∃ u ∈ dual_feasible_region A c, u ⬝ᵥ b < z := by
  let B := objective_threshold_matrix A c
  let r := objective_threshold_rhs b z
  have h_infeasible : ¬ ∃ x : Fin n → ℝ, B *ᵥ x ≤ r := by
    intro hx
    rcases hx with ⟨x, hx⟩
    have hx_primal : x ∈ primal_feasible_region A b := by
      rw [mem_primal_feasible_region_iff]
      intro i
      simpa [B, r, objective_threshold_matrix, objective_threshold_rhs, Matrix.mulVec, dotProduct]
        using hx i.succ
    have hz_le : z ≤ c ⬝ᵥ x := by
      have h0 : (B *ᵥ x) 0 ≤ r 0 := hx 0
      have h0' : ∑ i, (-c i) * x i ≤ -z := by
        simpa [B, r, objective_threshold_matrix, objective_threshold_rhs, Matrix.mulVec, dotProduct]
          using h0
      have h0'' : -(c ⬝ᵥ x) ≤ -z := by
        simpa [dotProduct, neg_mul, Finset.sum_neg_distrib] using h0'
      have : c ⬝ᵥ x ≥ z := by
        linarith
      exact this
    have hz_le_sup :
        (z : EReal) ≤
          sSup
            ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
              primal_feasible_region A b) := by
      exact (show (z : EReal) ≤ ((c ⬝ᵥ x : ℝ) : EReal) by exact_mod_cast hz_le).trans
        (le_sSup ⟨x, hx_primal, rfl⟩)
    exact (not_le_of_gt hz) hz_le_sup
  obtain ⟨y, hy⟩ := (farkas_lemma_linear_inequalities B r).mp h_infeasible
  let α : ℝ := y 0
  let uRaw : Fin m → ℝ := fun i ↦ y i.succ
  have hα_pos : 0 < α := by
    have hα_nonneg : 0 ≤ α := by
      simpa [α] using hy.nonneg 0
    by_contra hα_not_pos
    have hα_eq : α = 0 := by
      linarith
    have huRaw_cert : IsFarkasCertificate A b uRaw := by
      refine
        { nonneg := ?_
          annihilates := ?_
          negative_rhs := ?_ }
      · intro i
        simpa [uRaw] using hy.nonneg i.succ
      · ext j
        have hj0 : (y ᵥ* B) j = 0 := by
          simpa [B] using congrFun hy.annihilates j
        have hj : -α * c j + (uRaw ᵥ* A) j = 0 := by
          simpa [α, uRaw, B, vecMul_objective_threshold_matrix A c y] using hj0
        simpa [hα_eq] using hj
      · have hy_rhs : -α * z + uRaw ⬝ᵥ b < 0 := by
          simpa [α, uRaw, r, dotProduct_objective_threshold_rhs b z y] using hy.negative_rhs
        simpa [hα_eq] using hy_rhs
    rcases hP with ⟨x, hx⟩
    exact (farkas_certificate_excludes_solution huRaw_cert)
      ⟨x, (mem_primal_feasible_region_iff A b x).mp hx⟩
  have huRaw_eq : uRaw ᵥ* A = α • c := by
    ext j
    have hj0 : (y ᵥ* B) j = 0 := by
      simpa [B] using congrFun hy.annihilates j
    have hj' : -α * c j + (uRaw ᵥ* A) j = 0 := by
      simpa [α, uRaw, B, vecMul_objective_threshold_matrix A c y] using hj0
    have hj'' : (uRaw ᵥ* A) j = α * c j := by
      linarith
    simpa [Pi.smul_apply] using hj''
  let u : Fin m → ℝ := (1 / α) • uRaw
  have hu_mem : u ∈ dual_feasible_region A c := by
    rw [mem_dual_feasible_region_iff]
    constructor
    · calc
        u ᵥ* A = ((1 / α) • uRaw) ᵥ* A := by rfl
        _ = (1 / α) • (uRaw ᵥ* A) := by rw [Matrix.smul_vecMul]
        _ = (1 / α) • (α • c) := by rw [huRaw_eq]
        _ = c := by
          ext j
          simp [hα_pos.ne']
    · intro i
      exact smul_nonneg (one_div_nonneg.mpr hα_pos.le) (hy.nonneg i.succ)
  have hy_rhs : -α * z + uRaw ⬝ᵥ b < 0 := by
    simpa [α, uRaw, r, dotProduct_objective_threshold_rhs] using hy.negative_rhs
  have hu_lt : u ⬝ᵥ b < z := by
    have huRaw_lt : uRaw ⬝ᵥ b < α * z := by
      linarith
    have hu_div : (uRaw ⬝ᵥ b) / α < z := by
      have huRaw_lt' : uRaw ⬝ᵥ b < z * α := by
        simpa [mul_comm] using huRaw_lt
      exact (div_lt_iff₀ hα_pos).2 huRaw_lt'
    have hu_value : u ⬝ᵥ b = (uRaw ⬝ᵥ b) / α := by
      calc
        u ⬝ᵥ b = ((1 / α) • uRaw) ⬝ᵥ b := by rfl
        _ = (1 / α) • (uRaw ⬝ᵥ b) := by rw [smul_dotProduct]
        _ = (uRaw ⬝ᵥ b) / α := by
          simp [div_eq_mul_inv, mul_comm]
    rw [hu_value]
    exact hu_div
  exact ⟨u, hu_mem, hu_lt⟩

/-- Helper for Remark 3.10: when both feasible regions are nonempty, the extended-real primal
supremum equals the extended-real dual infimum. -/
lemma ereal_duality_eq_of_primal_dual_nonempty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : Set.Nonempty (primal_feasible_region A b))
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          primal_feasible_region A b) =
      sInf
        ((fun u : Fin m → ℝ ↦ ((u ⬝ᵥ b : ℝ) : EReal)) ''
          dual_feasible_region A c) := by
  let _ := hD
  have hle :
      sSup
          ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
            primal_feasible_region A b) ≤
        sInf
          ((fun u : Fin m → ℝ ↦ ((u ⬝ᵥ b : ℝ) : EReal)) ''
            dual_feasible_region A c) := by
    refine sSup_le ?_
    rintro _ ⟨x, hx, rfl⟩
    refine le_sInf ?_
    rintro _ ⟨u, hu, rfl⟩
    exact
      (show ((c ⬝ᵥ x : ℝ) : EReal) ≤ ((u ⬝ᵥ b : ℝ) : EReal) by
        exact_mod_cast weak_duality_feasible_pair A b c hx hu)
  refine le_antisymm hle (le_of_not_gt fun hlt ↦ ?_)
  obtain ⟨z, hz_left, hz_right⟩ := (EReal.lt_iff_exists_real_btwn).mp hlt
  obtain ⟨u, hu, huz⟩ := exists_dual_feasible_below_of_lt_primal_sup A b c hP hz_left
  have hz_lower : (z : EReal) ≤ ((u ⬝ᵥ b : ℝ) : EReal) := by
    exact hz_right.le.trans (sInf_le ⟨u, hu, rfl⟩)
  have huzE : ((u ⬝ᵥ b : ℝ) : EReal) < (z : EReal) := by
    simpa using huz
  exact (not_lt_of_ge hz_lower) huzE

/-- Helper for Remark 3.10: coercing a greatest real element into `EReal` preserves greatestness
for the coerced image set. -/
lemma isGreatest_ereal_image_of_isGreatest
    {s : Set ℝ}
    {r : ℝ}
    (hr : IsGreatest s r) :
    IsGreatest ((fun x : ℝ ↦ (x : EReal)) '' s) (r : EReal) := by
  -- The real-to-extended-real coercion is strictly monotone, so it preserves greatest elements.
  simpa using (StrictMono.map_isGreatest EReal.coe_strictMono).2 hr

/-- Helper for Remark 3.10: coercing a least real element into `EReal` preserves leastness for
the coerced image set. -/
lemma isLeast_ereal_image_of_isLeast
    {s : Set ℝ}
    {r : ℝ}
    (hr : IsLeast s r) :
    IsLeast ((fun x : ℝ ↦ (x : EReal)) '' s) (r : EReal) := by
  -- The same monotonicity argument transports least elements to the `EReal` image.
  simpa using (StrictMono.map_isLeast EReal.coe_strictMono).2 hr

/-- Helper for Remark 3.10: an unbounded-above real set has `EReal` supremum `⊤` after coercion.
-/
lemma ereal_sSup_eq_top_of_not_bddAbove
    {s : Set ℝ}
    (hs : ¬ BddAbove s) :
    sSup ((fun x : ℝ ↦ (x : EReal)) '' s) = ⊤ := by
  -- Any finite `EReal` threshold is exceeded by a real point because the original set is not
  -- bounded above.
  rw [sSup_eq_top]
  intro q hq
  rcases (EReal.lt_iff_exists_real_btwn).mp hq with ⟨r, hq_lt_r, hr_lt_top⟩
  rcases (not_bddAbove_iff.mp hs) r with ⟨x, hx, hrx⟩
  refine ⟨(x : EReal), ⟨x, hx, rfl⟩, ?_⟩
  have hrxE : (r : EReal) < (x : EReal) := by
    simpa using hrx
  exact hq_lt_r.trans hrxE

/-- Helper for Remark 3.10: an unbounded-below real set has `EReal` infimum `⊥` after coercion.
-/
lemma ereal_sInf_eq_bot_of_not_bddBelow
    {s : Set ℝ}
    (hs : ¬ BddBelow s) :
    sInf ((fun x : ℝ ↦ (x : EReal)) '' s) = ⊥ := by
  -- Dually, any finite `EReal` threshold above `⊥` is undershot by some real point.
  rw [sInf_eq_bot]
  intro q hq
  rcases (EReal.lt_iff_exists_real_btwn).mp hq with ⟨r, hbot_lt_r, hr_lt_q⟩
  rcases (not_bddBelow_iff.mp hs) r with ⟨x, hx, hxr⟩
  refine ⟨(x : EReal), ⟨x, hx, rfl⟩, ?_⟩
  have hxrE : (x : EReal) < (r : EReal) := by
    simpa using hxr
  exact hxrE.trans hr_lt_q

/-- Helper for Remark 3.10: if the primal system is infeasible but the dual region is nonempty,
then the dual objective values are unbounded below. -/
lemma dual_objective_values_not_bddBelow_of_primal_empty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (hP : ¬ Set.Nonempty (primal_feasible_region A b))
    (hD : Set.Nonempty (dual_feasible_region A c)) :
    ¬ BddBelow (dual_objective_values A b c) := by
  rcases hD with ⟨u₀, hu₀_mem⟩
  rcases (mem_dual_feasible_region_iff A c u₀).mp hu₀_mem with ⟨hu₀_eq, hu₀_nonneg⟩
  have h_infeasible : ¬ ∃ x : Fin n → ℝ, A *ᵥ x ≤ b := by
    -- Rephrase primal emptiness as infeasibility of the inequality system.
    intro hx
    rcases hx with ⟨x, hx⟩
    exact hP ⟨x, (mem_primal_feasible_region_iff A b x).2 hx⟩
  obtain ⟨y, hy⟩ := (farkas_lemma_linear_inequalities A b).mp h_infeasible
  intro hbounded
  rcases hbounded with ⟨M, hM⟩
  have hyb_neg : y ⬝ᵥ b < 0 := hy.negative_rhs
  have hyb_pos : 0 < -(y ⬝ᵥ b) := by
    linarith
  obtain ⟨N, hN⟩ : ∃ N : ℕ, (u₀ ⬝ᵥ b - M) / (-(y ⬝ᵥ b)) < N := by
    exact exists_nat_gt ((u₀ ⬝ᵥ b - M) / (-(y ⬝ᵥ b)))
  have hNmul : u₀ ⬝ᵥ b - M < (N : ℝ) * (-(y ⬝ᵥ b)) := by
    exact (div_lt_iff₀ hyb_pos).mp hN
  let uN : Fin m → ℝ := u₀ + (N : ℝ) • y
  have huN_mem : uN ∈ dual_feasible_region A c := by
    rw [mem_dual_feasible_region_iff]
    constructor
    · -- Adding a left-kernel certificate preserves the dual equality constraint.
      calc
        uN ᵥ* A = u₀ ᵥ* A + ((N : ℝ) • y) ᵥ* A := by
          simpa [uN] using Matrix.add_vecMul A u₀ ((N : ℝ) • y)
        _ = c + (N : ℝ) • (y ᵥ* A) := by
          rw [Matrix.smul_vecMul, hu₀_eq]
        _ = c := by
          simp [hy.annihilates]
    · -- Nonnegativity is preserved because the Farkas certificate is nonnegative.
      intro i
      have hN_nonneg : 0 ≤ (N : ℝ) := by
        exact_mod_cast Nat.zero_le N
      exact add_nonneg (hu₀_nonneg i) (smul_nonneg hN_nonneg (hy.nonneg i))
  have huN_value :
      uN ⬝ᵥ b = u₀ ⬝ᵥ b + (N : ℝ) * (y ⬝ᵥ b) := by
    -- The dual objective along the ray is affine in the ray parameter.
    calc
      uN ⬝ᵥ b = (u₀ + (N : ℝ) • y) ⬝ᵥ b := by rfl
      _ = u₀ ⬝ᵥ b + ((N : ℝ) • y) ⬝ᵥ b := by
        rw [add_dotProduct]
      _ = u₀ ⬝ᵥ b + (N : ℝ) * (y ⬝ᵥ b) := by
        rw [smul_dotProduct]
        simp [smul_eq_mul]
  have huN_below : uN ⬝ᵥ b < M := by
    -- Choosing `N` large enough forces the objective value below the putative lower bound.
    rw [huN_value]
    linarith
  exact (not_lt_of_ge (hM ⟨uN, huN_mem, rfl⟩)) huN_below

/-- Remark 3.10. For the primal region `P = {x | A *ᵥ x ≤ b}` and the dual region
`D = {u | u ᵥ* A = c ∧ 0 ≤ u}`, the duality equation between the primal maximum and dual
minimum holds in the extended reals in every case except when `P` and `D` are both empty. -/
theorem linear_program_duality_eq_except_both_empty
    {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ)
    (c : Fin n → ℝ)
    (h_nonempty :
      Set.Nonempty (primal_feasible_region A b) ∨
        Set.Nonempty (dual_feasible_region A c)) :
    sSup
        ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
          primal_feasible_region A b) =
      sInf
        ((fun u : Fin m → ℝ ↦ ((u ⬝ᵥ b : ℝ) : EReal)) ''
          dual_feasible_region A c) := by
  by_cases hP : Set.Nonempty (primal_feasible_region A b)
  · by_cases hD : Set.Nonempty (dual_feasible_region A c)
    · exact ereal_duality_eq_of_primal_dual_nonempty A b c hP hD
    · have hD_empty : dual_feasible_region A c = (∅ : Set (Fin m → ℝ)) := by
        rwa [Set.not_nonempty_iff_eq_empty] at hD
      have hPrimalUnbounded : ¬ BddAbove (primal_objective_values A b c) := by
        rw [primal_objective_unbounded_iff_dual_feasible_region_empty A b c hP]
        exact hD_empty
      have hPrimalTop :
          sSup
              ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
                primal_feasible_region A b) = ⊤ := by
        -- Proposition 3.9 turns dual emptiness into primal unboundedness.
        simpa [primal_objective_values, Set.image_image] using
          ereal_sSup_eq_top_of_not_bddAbove hPrimalUnbounded
      have hDualTop :
          sInf
              ((fun u : Fin m → ℝ ↦ ((u ⬝ᵥ b : ℝ) : EReal)) ''
                dual_feasible_region A c) = ⊤ := by
        -- The empty dual feasible region gives the convention `min ∅ = +∞`.
        simp [hD_empty]
      exact hPrimalTop.trans hDualTop.symm
  · have hP_empty : primal_feasible_region A b = (∅ : Set (Fin n → ℝ)) := by
      rwa [Set.not_nonempty_iff_eq_empty] at hP
    have hD : Set.Nonempty (dual_feasible_region A c) := by
      rcases h_nonempty with hP' | hD'
      · exact False.elim (hP hP')
      · exact hD'
    have hDualUnbounded : ¬ BddBelow (dual_objective_values A b c) :=
      dual_objective_values_not_bddBelow_of_primal_empty A b c hP hD
    have hPrimalBot :
        sSup
            ((fun x : Fin n → ℝ ↦ ((c ⬝ᵥ x : ℝ) : EReal)) ''
              primal_feasible_region A b) = ⊥ := by
      -- The empty primal feasible region gives the convention `max ∅ = -∞`.
      simp [hP_empty]
    have hDualBot :
        sInf
            ((fun u : Fin m → ℝ ↦ ((u ⬝ᵥ b : ℝ) : EReal)) ''
              dual_feasible_region A c) = ⊥ := by
      -- The Farkas certificate produces a dual-feasible ray with objective tending to `-∞`.
      simpa [dual_objective_values, Set.image_image] using
        ereal_sInf_eq_bot_of_not_bddBelow hDualUnbounded
    exact hPrimalBot.trans hDualBot.symm
